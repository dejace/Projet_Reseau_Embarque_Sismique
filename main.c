/* USER CODE BEGIN Header */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "cmsis_os.h"
#include "lwip.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include <stdlib.h>   // atof()
#include "lwip/udp.h"
#include "lwip/ip_addr.h"
#include "lwip/netif.h"
#include "lwip/timeouts.h"   // sys_now()
#include "lwip/api.h"     // netconn_*
#include "lwip/sys.h"


/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */
/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */
#define RMS_TOP_N              10
#define MAX_NODES              8

#define SEISM_RMS_THRESHOLD    1200.0f   // <-- à calibrer
#define VALIDATION_WINDOW_MS   2500      // fenêtre de temps pour considérer les RMS "simultanées"
#define REQUIRED_PEERS         1         // nb minimum de pairs au-dessus du seuil (en plus de toi)


#define SAMPLE_RATE_HZ     100
#define WINDOW_SIZE        SAMPLE_RATE_HZ   // 1 seconde
#define TCP_PORT_DATA      5000
#define TCP_RX_TIMEOUT_MS  2000
/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */
/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
DMA_HandleTypeDef hdma_adc1;

RTC_HandleTypeDef hrtc;

TIM_HandleTypeDef htim2;

UART_HandleTypeDef huart3;

osThreadId defaultTaskHandle;
osThreadId logMessageTaskHandle;
osThreadId clientTaskHandle;
osThreadId serverTaskHandle;
osThreadId heartBeatTaskHandle;
osMessageQId messageQueueHandle;
osMutexId uartMutexHandle;
/* USER CODE BEGIN PV */
static float mag_buffer[WINDOW_SIZE];
static uint16_t mag_index = 0;
static uint8_t mag_filled = 0;

static float rms_1s = 0.0f;
static float mean_1s = 0.0f;
// ====== ADC DMA acquisition ======
static uint16_t adc_dma_buf[3];          // 3 axes (X,Y,Z)
static volatile uint32_t sample_counter = 0;

// Handle FreeRTOS pour notifier la tâche d'acquisition depuis l'ISR
static TaskHandle_t acquisitionTaskHandle_freertos = NULL;

// ====== Réseau prêt ? ======
static volatile uint8_t net_ready = 0;

// ====== UDP presence ======
static struct udp_pcb *presence_pcb = NULL;

// ====== ID nœud ======
static const char *NODE_ID = "nucleo-11";
osThreadId tcpServerTaskHandle;
osThreadId tcpClientTaskHandle;
typedef struct {
    char id[16];               // ex: "nucleo-01"
    ip_addr_t ip;
    uint8_t used;

    float top_rms[RMS_TOP_N];  // les 10 max RMS pour CE noeud
    uint8_t top_count;

    float last_rms;            // dernière RMS reçue
    uint32_t last_ms;          // timestamp sys_now() associé
} node_info_t;

static node_info_t nodes[MAX_NODES];

// Historique local (ton propre noeud)
static float local_top_rms[RMS_TOP_N];
static uint8_t local_top_count = 0;

// Etat de détection locale
static volatile uint8_t local_shake = 0;
static volatile uint32_t local_shake_ms = 0;

/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_DMA_Init(void);
static void MX_USART3_UART_Init(void);
static void MX_RTC_Init(void);
static void MX_ADC1_Init(void);
static void MX_TIM2_Init(void);
void StartDefaultTask(void const * argument);
void LogMessageTask(void const * argument);
void StartClientTask(void const * argument);
void StartServerTask(void const * argument);
void StartHeartBeatTask(void const * argument);

/* USER CODE BEGIN PFP */
void StartTcpServerTask(void const *argument);
void StartTcpClientTask(void const *argument);
static void top10_insert(float *arr, uint8_t *count, float v);
static node_info_t* get_or_create_node(const char *id, const ip_addr_t *ip);
static int parse_json_id_rms(const char *json, char *out_id, size_t out_id_sz, float *out_rms);

/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */


static void log_enqueue(const char *fmt, ...) {
	// Alloue un message (pointeur envoyé dans la queue)
	char *msg = (char*) pvPortMalloc(160);
	if (!msg)
		return;

	va_list args;
	va_start(args, fmt);
	vsnprintf(msg, 160, fmt, args);
	va_end(args);

	// On push le pointeur dans la queue CMSIS (uint32_t)
	osMessagePut(messageQueueHandle, (uint32_t) msg, 0);
}
static void process_seismic(uint16_t x, uint16_t y, uint16_t z) {
	float fx = (float) x;
	float fy = (float) y;
	float fz = (float) z;
	float mag = sqrtf(fx * fx + fy * fy + fz * fz);

	mag_buffer[mag_index++] = mag;

	if (mag_index >= WINDOW_SIZE) {
		mag_index = 0;
		mag_filled = 1;
	}

	if (!mag_filled)
		return;

	float sum = 0.0f;
	float sum_sq = 0.0f;

	for (int i = 0; i < WINDOW_SIZE; i++) {
		sum += mag_buffer[i];
		sum_sq += mag_buffer[i] * mag_buffer[i];
	}

	mean_1s = sum / WINDOW_SIZE;
	rms_1s = sqrtf(sum_sq / WINDOW_SIZE);
}
static void tcp_server_thread(void) {
	struct netconn *conn = netconn_new(NETCONN_TCP);
	if (!conn) {
		log_enqueue("[TCP] netconn_new failed\r\n");
		return;
	}

	if (netconn_bind(conn, IP_ADDR_ANY, TCP_PORT_DATA) != ERR_OK) {
		log_enqueue("[TCP] bind failed\r\n");
		netconn_delete(conn);
		return;
	}

	netconn_listen(conn);
	log_enqueue("[TCP] Listening on %d\r\n", TCP_PORT_DATA);

	while (1) {
		struct netconn *newconn;
		err_t err = netconn_accept(conn, &newconn);
		if (err == ERR_OK && newconn) {
			netconn_set_recvtimeout(newconn, TCP_RX_TIMEOUT_MS);
			struct netbuf *buf;
			void *data;
			u16_t len;

			// attend une requête (ex: "GET\n")
			err = netconn_recv(newconn, &buf);
			if (err == ERR_OK && buf) {
				netbuf_data(buf, &data, &len);

				// Si le client envoie "GET"
				if (len >= 3 && memcmp(data, "GET", 3) == 0) {
					uint16_t ax = adc_dma_buf[0];
					uint16_t ay = adc_dma_buf[1];
					uint16_t az = adc_dma_buf[2];

					char tx[256];
					snprintf(tx, sizeof(tx),
							"{ \"type\":\"data\", \"id\":\"%s\", \"x\":%u, \"y\":%u, \"z\":%u, \"mean_1s\":%.2f, \"rms_1s\":%.2f, \"t_ms\":%lu }\n",
							NODE_ID, ax, ay, az, mean_1s, rms_1s,
							(unsigned long) sys_now());

					netconn_write(newconn, tx, strlen(tx), NETCONN_COPY);
				} else {
					const char *bad = "ERR\n";
					netconn_write(newconn, bad, strlen(bad), NETCONN_COPY);
				}

				netbuf_delete(buf);
			}

			netconn_close(newconn);
			netconn_delete(newconn);
		}

		osDelay(5);
	}
}
void StartTcpServerTask(void const *argument) {
	while (!net_ready)
		osDelay(50);
	tcp_server_thread();
}
static void tcp_request_to(ip_addr_t *ip) {
	struct netconn *c = netconn_new(NETCONN_TCP);
	if (!c)
		return;

	if (netconn_connect(c, ip, TCP_PORT_DATA) == ERR_OK) {
		netconn_set_recvtimeout(c, TCP_RX_TIMEOUT_MS);
		const char *req = "GET\n";
		netconn_write(c, req, strlen(req), NETCONN_COPY);

		struct netbuf *buf;
		err_t err = netconn_recv(c, &buf);
		if (err == ERR_OK && buf) {
			void *data;
			u16_t len;
			netbuf_data(buf, &data, &len);

			char rx[300];
			u16_t cpy = (len < sizeof(rx) - 1) ? len : (sizeof(rx) - 1);
			memcpy(rx, data, cpy);
			rx[cpy] = 0;
			char nid[16];
			float rrms;

			if (parse_json_id_rms(rx, nid, sizeof(nid), &rrms)) {
			    node_info_t *n = get_or_create_node(nid, ip);
			    if (n) {
			        n->last_rms = rrms;
			        n->last_ms  = sys_now();
			        top10_insert(n->top_rms, &n->top_count, rrms);
			    }

			    log_enqueue("[TCP-CLIENT] %s rms=%.2f\r\n", nid, rrms);
			} else {
			    log_enqueue("[TCP-CLIENT] RX (unparsed)=%s\r\n", rx);
			}
			netbuf_delete(buf);
		}
	}

	netconn_close(c);
	netconn_delete(c);
}

void StartTcpClientTask(void const *argument) {
	while (!net_ready)
		osDelay(50);

	// Exemple: IP fixe d’un autre noeud (à adapter)
	static const char *peer_ips[] = {
	    "192.168.10.100",
	    // ajoute ici les autres cartes
	};
	static const int peer_count = sizeof(peer_ips)/sizeof(peer_ips[0]);

	for (;;) {
	    for (int i = 0; i < peer_count; i++) {
	        ip_addr_t target;
	        ip4addr_aton(peer_ips[i], ip_2_ip4(&target));
	        tcp_request_to(&target);
	        osDelay(50);
	    }
	    osDelay(500);
	}

}
static void top10_insert(float *arr, uint8_t *count, float v)
{
    // si pas assez de valeurs, on ajoute puis on trie
    if (*count < RMS_TOP_N) {
        arr[*count] = v;
        (*count)++;
    } else {
        // si v <= plus petite (arr[RMS_TOP_N-1] après tri décroissant), on ignore
        if (v <= arr[RMS_TOP_N - 1]) return;
        arr[RMS_TOP_N - 1] = v;
    }

    // tri décroissant simple (RMS_TOP_N <= 10 donc c’est OK)
    for (int i = 0; i < (int)(*count) - 1; i++) {
        for (int j = i + 1; j < (int)(*count); j++) {
            if (arr[j] > arr[i]) {
                float tmp = arr[i];
                arr[i] = arr[j];
                arr[j] = tmp;
            }
        }
    }
}
static node_info_t* get_or_create_node(const char *id, const ip_addr_t *ip)
{
    // Cherche existant
    for (int i = 0; i < MAX_NODES; i++) {
        if (nodes[i].used && strncmp(nodes[i].id, id, sizeof(nodes[i].id)) == 0) {
            if (ip) nodes[i].ip = *ip;
            return &nodes[i];
        }
    }
    // Crée nouveau
    for (int i = 0; i < MAX_NODES; i++) {
        if (!nodes[i].used) {
            memset(&nodes[i], 0, sizeof(nodes[i]));
            nodes[i].used = 1;
            strncpy(nodes[i].id, id, sizeof(nodes[i].id) - 1);
            if (ip) nodes[i].ip = *ip;
            return &nodes[i];
        }
    }
    return NULL; // table pleine
}
static int parse_json_id_rms(const char *json, char *out_id, size_t out_id_sz, float *out_rms)
{
    const char *pid = strstr(json, "\"id\":\"");
    const char *prms = strstr(json, "\"rms_1s\":");
    if (!pid || !prms) return 0;

    pid += strlen("\"id\":\"");
    const char *pid_end = strchr(pid, '"');
    if (!pid_end) return 0;

    size_t n = (size_t)(pid_end - pid);
    if (n >= out_id_sz) n = out_id_sz - 1;
    memcpy(out_id, pid, n);
    out_id[n] = 0;

    prms += strlen("\"rms_1s\":");
    *out_rms = (float)atof(prms);
    return 1;
}

/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{

  /* USER CODE BEGIN 1 */
  /* USER CODE END 1 */

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */
  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */
  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  MX_DMA_Init();
  MX_USART3_UART_Init();
  MX_RTC_Init();
  MX_ADC1_Init();
  MX_TIM2_Init();
  /* USER CODE BEGIN 2 */
  /* USER CODE END 2 */

  /* Create the mutex(es) */
  /* definition and creation of uartMutex */
  osMutexDef(uartMutex);
  uartMutexHandle = osMutexCreate(osMutex(uartMutex));

  /* USER CODE BEGIN RTOS_MUTEX */
  /* USER CODE END RTOS_MUTEX */

  /* USER CODE BEGIN RTOS_SEMAPHORES */
  /* USER CODE END RTOS_SEMAPHORES */

  /* USER CODE BEGIN RTOS_TIMERS */
  /* USER CODE END RTOS_TIMERS */

  /* Create the queue(s) */
  /* definition and creation of messageQueue */
  osMessageQDef(messageQueue, 16, uint32_t);
  messageQueueHandle = osMessageCreate(osMessageQ(messageQueue), NULL);

  /* USER CODE BEGIN RTOS_QUEUES */
  /* USER CODE END RTOS_QUEUES */

  /* Create the thread(s) */
  /* definition and creation of defaultTask */
  osThreadDef(defaultTask, StartDefaultTask, osPriorityNormal, 0, 256);
  defaultTaskHandle = osThreadCreate(osThread(defaultTask), NULL);

  /* definition and creation of logMessageTask */
  osThreadDef(logMessageTask, LogMessageTask, osPriorityNormal, 0, 256);
  logMessageTaskHandle = osThreadCreate(osThread(logMessageTask), NULL);

  /* definition and creation of clientTask */
  osThreadDef(clientTask, StartClientTask, osPriorityBelowNormal, 0, 256);
  clientTaskHandle = osThreadCreate(osThread(clientTask), NULL);

  /* definition and creation of serverTask */
  osThreadDef(serverTask, StartServerTask, osPriorityBelowNormal, 0, 256);
  serverTaskHandle = osThreadCreate(osThread(serverTask), NULL);

  /* definition and creation of heartBeatTask */
  osThreadDef(heartBeatTask, StartHeartBeatTask, osPriorityIdle, 0, 256);
  heartBeatTaskHandle = osThreadCreate(osThread(heartBeatTask), NULL);

  /* USER CODE BEGIN RTOS_THREADS */
	osThreadDef(tcpServerTask, StartTcpServerTask, osPriorityBelowNormal, 0,
			512);
	tcpServerTaskHandle = osThreadCreate(osThread(tcpServerTask), NULL);

	osThreadDef(tcpClientTask, StartTcpClientTask, osPriorityBelowNormal, 0,
			512);
	tcpClientTaskHandle = osThreadCreate(osThread(tcpClientTask), NULL);
  /* USER CODE END RTOS_THREADS */

  /* Start scheduler */
  osKernelStart();

  /* We should never get here as control is now taken by the scheduler */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
  /* USER CODE END 3 */
}

/**
  * @brief System Clock Configuration
  * @retval None
  */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};

  /** Configure the main internal regulator output voltage
  */
  __HAL_RCC_PWR_CLK_ENABLE();
  __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE3);

  /** Initializes the RCC Oscillators according to the specified parameters
  * in the RCC_OscInitTypeDef structure.
  */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI|RCC_OSCILLATORTYPE_LSI;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
  RCC_OscInitStruct.LSIState = RCC_LSI_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSI;
  RCC_OscInitStruct.PLL.PLLM = 16;
  RCC_OscInitStruct.PLL.PLLN = 192;
  RCC_OscInitStruct.PLL.PLLP = RCC_PLLP_DIV4;
  RCC_OscInitStruct.PLL.PLLQ = 2;
  RCC_OscInitStruct.PLL.PLLR = 2;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }

  /** Initializes the CPU, AHB and APB buses clocks
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV4;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV2;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_1) != HAL_OK)
  {
    Error_Handler();
  }
}

/**
  * @brief ADC1 Initialization Function
  * @param None
  * @retval None
  */
static void MX_ADC1_Init(void)
{

  /* USER CODE BEGIN ADC1_Init 0 */

  /* USER CODE END ADC1_Init 0 */

  ADC_ChannelConfTypeDef sConfig = {0};

  /* USER CODE BEGIN ADC1_Init 1 */

  /* USER CODE END ADC1_Init 1 */

  /** Configure the global features of the ADC (Clock, Resolution, Data Alignment and number of conversion)
  */
  hadc1.Instance = ADC1;
  hadc1.Init.ClockPrescaler = ADC_CLOCK_SYNC_PCLK_DIV2;
  hadc1.Init.Resolution = ADC_RESOLUTION_12B;
  hadc1.Init.ScanConvMode = ADC_SCAN_ENABLE;
  hadc1.Init.ContinuousConvMode = DISABLE;
  hadc1.Init.DiscontinuousConvMode = DISABLE;
  hadc1.Init.ExternalTrigConvEdge = ADC_EXTERNALTRIGCONVEDGE_RISING;
  hadc1.Init.ExternalTrigConv = ADC_EXTERNALTRIGCONV_T2_TRGO;
  hadc1.Init.DataAlign = ADC_DATAALIGN_RIGHT;
  hadc1.Init.NbrOfConversion = 3;
  hadc1.Init.DMAContinuousRequests = ENABLE;
  hadc1.Init.EOCSelection = ADC_EOC_SINGLE_CONV;
  if (HAL_ADC_Init(&hadc1) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_4;
  sConfig.Rank = ADC_REGULAR_RANK_1;
  sConfig.SamplingTime = ADC_SAMPLETIME_3CYCLES;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Rank = ADC_REGULAR_RANK_2;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Rank = ADC_REGULAR_RANK_3;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN ADC1_Init 2 */

  /* USER CODE END ADC1_Init 2 */

}

/**
  * @brief RTC Initialization Function
  * @param None
  * @retval None
  */
static void MX_RTC_Init(void)
{

  /* USER CODE BEGIN RTC_Init 0 */
  /* USER CODE END RTC_Init 0 */

  RTC_TimeTypeDef sTime = {0};
  RTC_DateTypeDef sDate = {0};

  /* USER CODE BEGIN RTC_Init 1 */
  /* USER CODE END RTC_Init 1 */

  /** Initialize RTC Only
  */
  hrtc.Instance = RTC;
  hrtc.Init.HourFormat = RTC_HOURFORMAT_24;
  hrtc.Init.AsynchPrediv = 127;
  hrtc.Init.SynchPrediv = 255;
  hrtc.Init.OutPut = RTC_OUTPUT_DISABLE;
  hrtc.Init.OutPutPolarity = RTC_OUTPUT_POLARITY_HIGH;
  hrtc.Init.OutPutType = RTC_OUTPUT_TYPE_OPENDRAIN;
  if (HAL_RTC_Init(&hrtc) != HAL_OK)
  {
    Error_Handler();
  }

  /* USER CODE BEGIN Check_RTC_BKUP */
  /* USER CODE END Check_RTC_BKUP */

  /** Initialize RTC and set the Time and Date
  */
  sTime.Hours = 0x0;
  sTime.Minutes = 0x0;
  sTime.Seconds = 0x0;
  sTime.DayLightSaving = RTC_DAYLIGHTSAVING_NONE;
  sTime.StoreOperation = RTC_STOREOPERATION_RESET;
  if (HAL_RTC_SetTime(&hrtc, &sTime, RTC_FORMAT_BCD) != HAL_OK)
  {
    Error_Handler();
  }
  sDate.WeekDay = RTC_WEEKDAY_MONDAY;
  sDate.Month = RTC_MONTH_JANUARY;
  sDate.Date = 0x1;
  sDate.Year = 0x0;

  if (HAL_RTC_SetDate(&hrtc, &sDate, RTC_FORMAT_BCD) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN RTC_Init 2 */
  /* USER CODE END RTC_Init 2 */

}

/**
  * @brief TIM2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_TIM2_Init(void)
{

  /* USER CODE BEGIN TIM2_Init 0 */

  /* USER CODE END TIM2_Init 0 */

  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};

  /* USER CODE BEGIN TIM2_Init 1 */

  /* USER CODE END TIM2_Init 1 */
  htim2.Instance = TIM2;
  htim2.Init.Prescaler = 2399;
  htim2.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim2.Init.Period = 99;
  htim2.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim2.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim2) != HAL_OK)
  {
    Error_Handler();
  }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim2, &sClockSourceConfig) != HAL_OK)
  {
    Error_Handler();
  }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_UPDATE;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim2, &sMasterConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN TIM2_Init 2 */

  /* USER CODE END TIM2_Init 2 */

}

/**
  * @brief USART3 Initialization Function
  * @param None
  * @retval None
  */
static void MX_USART3_UART_Init(void)
{

  /* USER CODE BEGIN USART3_Init 0 */
  /* USER CODE END USART3_Init 0 */

  /* USER CODE BEGIN USART3_Init 1 */
  /* USER CODE END USART3_Init 1 */
  huart3.Instance = USART3;
  huart3.Init.BaudRate = 115200;
  huart3.Init.WordLength = UART_WORDLENGTH_8B;
  huart3.Init.StopBits = UART_STOPBITS_1;
  huart3.Init.Parity = UART_PARITY_NONE;
  huart3.Init.Mode = UART_MODE_TX_RX;
  huart3.Init.HwFlowCtl = UART_HWCONTROL_NONE;
  huart3.Init.OverSampling = UART_OVERSAMPLING_16;
  huart3.Init.OneBitSampling = UART_ONE_BIT_SAMPLE_DISABLE;
  huart3.AdvancedInit.AdvFeatureInit = UART_ADVFEATURE_NO_INIT;
  if (HAL_UART_Init(&huart3) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN USART3_Init 2 */
  /* USER CODE END USART3_Init 2 */

}

/**
  * Enable DMA controller clock
  */
static void MX_DMA_Init(void)
{

  /* DMA controller clock enable */
  __HAL_RCC_DMA2_CLK_ENABLE();

  /* DMA interrupt init */
  /* DMA2_Stream0_IRQn interrupt configuration */
  HAL_NVIC_SetPriority(DMA2_Stream0_IRQn, 5, 0);
  HAL_NVIC_EnableIRQ(DMA2_Stream0_IRQn);

}

/**
  * @brief GPIO Initialization Function
  * @param None
  * @retval None
  */
static void MX_GPIO_Init(void)
{
  GPIO_InitTypeDef GPIO_InitStruct = {0};
  /* USER CODE BEGIN MX_GPIO_Init_1 */
  /* USER CODE END MX_GPIO_Init_1 */

  /* GPIO Ports Clock Enable */
  __HAL_RCC_GPIOC_CLK_ENABLE();
  __HAL_RCC_GPIOH_CLK_ENABLE();
  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();
  __HAL_RCC_GPIOD_CLK_ENABLE();
  __HAL_RCC_GPIOG_CLK_ENABLE();

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(GPIOB, LD1_Pin|LD3_Pin|LD2_Pin, GPIO_PIN_RESET);

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(USB_PowerSwitchOn_GPIO_Port, USB_PowerSwitchOn_Pin, GPIO_PIN_RESET);

  /*Configure GPIO pin : USER_Btn_Pin */
  GPIO_InitStruct.Pin = USER_Btn_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_IT_RISING;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(USER_Btn_GPIO_Port, &GPIO_InitStruct);

  /*Configure GPIO pins : LD1_Pin LD3_Pin LD2_Pin */
  GPIO_InitStruct.Pin = LD1_Pin|LD3_Pin|LD2_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

  /*Configure GPIO pin : USB_PowerSwitchOn_Pin */
  GPIO_InitStruct.Pin = USB_PowerSwitchOn_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(USB_PowerSwitchOn_GPIO_Port, &GPIO_InitStruct);

  /*Configure GPIO pin : USB_OverCurrent_Pin */
  GPIO_InitStruct.Pin = USB_OverCurrent_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(USB_OverCurrent_GPIO_Port, &GPIO_InitStruct);

  /*Configure GPIO pins : USB_SOF_Pin USB_ID_Pin USB_DM_Pin USB_DP_Pin */
  GPIO_InitStruct.Pin = USB_SOF_Pin|USB_ID_Pin|USB_DM_Pin|USB_DP_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_AF_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_VERY_HIGH;
  GPIO_InitStruct.Alternate = GPIO_AF10_OTG_FS;
  HAL_GPIO_Init(GPIOA, &GPIO_InitStruct);

  /*Configure GPIO pin : USB_VBUS_Pin */
  GPIO_InitStruct.Pin = USB_VBUS_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(USB_VBUS_GPIO_Port, &GPIO_InitStruct);

  /* USER CODE BEGIN MX_GPIO_Init_2 */
  /* USER CODE END MX_GPIO_Init_2 */
}

/* USER CODE BEGIN 4 */
void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef *hadc) {
	if (hadc->Instance == ADC1) {
		BaseType_t xHigherPriorityTaskWoken = pdFALSE;
		sample_counter++;

		if (acquisitionTaskHandle_freertos != NULL) {
			vTaskNotifyGiveFromISR(acquisitionTaskHandle_freertos,
					&xHigherPriorityTaskWoken);
			portYIELD_FROM_ISR(xHigherPriorityTaskWoken);
		}
	}
}

/* USER CODE END 4 */

/* USER CODE BEGIN Header_StartDefaultTask */
/* USER CODE END Header_StartDefaultTask */
/* USER CODE BEGIN 5 */
void StartDefaultTask(void const * argument)
{
  MX_LWIP_Init();

  net_ready = 1;

  for (;;)
  {
    osDelay(1000);
  }


  /* USER CODE END 5 */
}


/* USER CODE BEGIN Header_LogMessageTask */
/* USER CODE END Header_LogMessageTask */
void LogMessageTask(void const * argument)
{
  /* USER CODE BEGIN LogMessageTask */
	for (;;) {
		osEvent evt = osMessageGet(messageQueueHandle, osWaitForever);
		if (evt.status == osEventMessage) {
			char *msg = (char*) evt.value.v;
			if (msg) {
				osMutexWait(uartMutexHandle, osWaitForever);
				HAL_UART_Transmit(&huart3, (uint8_t*) msg,
						(uint16_t) strlen(msg), 200);
				osMutexRelease(uartMutexHandle);

				vPortFree(msg);
			}
		}
	}
  /* USER CODE END LogMessageTask */
}

/* USER CODE BEGIN Header_StartClientTask */
/* USER CODE END Header_StartClientTask */
void StartClientTask(void const * argument)
{
  /* USER CODE BEGIN StartClientTask */
	// Attendre que le réseau soit prêt
	while (!net_ready)
		osDelay(50);

	extern struct netif gnetif;

	presence_pcb = udp_new_ip_type(IPADDR_TYPE_V4);
	if (!presence_pcb) {
		log_enqueue("[PRESENCE] ERROR: udp_new failed\r\n");
		for (;;)
			osDelay(1000);
	}

	// if (!presence_pcb)
	//{
	// log_enqueue("[PRESENCE] ERROR: udp_new\r\n");
	//for(;;) osDelay(1000);
	//}

	// Autoriser broadcast
	ip_set_option(presence_pcb, SOF_BROADCAST);

	const uint16_t port = 12345;

	for (;;) {
		// JSON minimal (timestamp = uptime ms)
		char payload[220];
		snprintf(payload, sizeof(payload),
				"{ \"type\":\"presence\", \"id\":\"%s\", \"ip\":\"%s\", \"timestamp_ms\":%lu }\r\n",
				NODE_ID, ip4addr_ntoa(netif_ip4_addr(&gnetif)),
				(unsigned long) sys_now());

		struct pbuf *p = pbuf_alloc(PBUF_TRANSPORT, (uint16_t) strlen(payload),
				PBUF_RAM);
		if (p) {
			memcpy(p->payload, payload, strlen(payload));

			ip_addr_t bcast;
			ip4addr_aton("255.255.255.255", ip_2_ip4(&bcast));

			udp_sendto(presence_pcb, p, &bcast, port);
			pbuf_free(p);

			log_enqueue("[PRESENCE] broadcast sent\r\n");
		}

		osDelay(10000); // 10s
	}
  /* USER CODE END StartClientTask */
}

/* USER CODE BEGIN Header_StartServerTask */
/* USER CODE END Header_StartServerTask */
void StartServerTask(void const * argument)
{
  /* USER CODE BEGIN StartServerTask */
	// On garde le handle FreeRTOS pour les notifications ISR
	acquisitionTaskHandle_freertos = xTaskGetCurrentTaskHandle();

	// Démarre TIM2 (TRGO) + ADC DMA
	HAL_TIM_Base_Start(&htim2);

	// Démarre ADC en DMA sur 3 valeurs
	if (HAL_ADC_Start_DMA(&hadc1, (uint32_t*) adc_dma_buf, 3) != HAL_OK) {
		log_enqueue("[ADC] ERROR: HAL_ADC_Start_DMA\r\n");
	} else {
		log_enqueue("[ADC] DMA started (3ch) @100Hz via TIM2 TRGO\r\n");
	}

	for (;;)
	{
	  ulTaskNotifyTake(pdTRUE, portMAX_DELAY);

	  uint16_t ax = adc_dma_buf[0];
	  uint16_t ay = adc_dma_buf[1];
	  uint16_t az = adc_dma_buf[2];

	  process_seismic(ax, ay, az);
	  top10_insert(local_top_rms, &local_top_count, rms_1s);
	  // Détection locale
	  if (rms_1s >= SEISM_RMS_THRESHOLD) {
	      local_shake = 1;
	      local_shake_ms = sys_now();

	      // Validation: combien de pairs ont aussi dépassé le seuil dans la même fenêtre ?
	      int peers_ok = 0;
	      uint32_t now = sys_now();

	      for (int i = 0; i < MAX_NODES; i++) {
	          if (!nodes[i].used) continue;

	          // RMS "récente" ?
	          if ((now - nodes[i].last_ms) <= VALIDATION_WINDOW_MS) {
	              if (nodes[i].last_rms >= SEISM_RMS_THRESHOLD) {
	                  peers_ok++;
	              }
	          }
	      }

	      if (peers_ok >= REQUIRED_PEERS) {
	          // => Secousse validée collectivement
	          log_enqueue("[ALERT] Seisme valide ! local rms=%.2f peers_ok=%d\r\n", rms_1s, peers_ok);

	          // Allume une LED d'alarme (choisis LD2 par ex, différente du heartbeat LD1)
	          HAL_GPIO_WritePin(LD2_GPIO_Port, LD2_Pin, GPIO_PIN_SET);
	      } else {
	          // Pas validé
	          HAL_GPIO_WritePin(LD2_GPIO_Port, LD2_Pin, GPIO_PIN_RESET);
	      }
	  } else {
	      local_shake = 0;
	      HAL_GPIO_WritePin(LD2_GPIO_Port, LD2_Pin, GPIO_PIN_RESET);
	  }


	  if ((sample_counter % 100) == 0) // 1 Hz
	  {
	    log_enqueue("ADC: X=%u Y=%u Z=%u | mean=%.2f rms=%.2f | t=%lu\r\n",
	                ax, ay, az, mean_1s, rms_1s, (unsigned long)sys_now());
	  }
	}
  /* USER CODE END StartServerTask */
}

/* USER CODE BEGIN Header_StartHeartBeatTask */
/* USER CODE END Header_StartHeartBeatTask */
void StartHeartBeatTask(void const * argument)
{
  /* USER CODE BEGIN StartHeartBeatTask */
	for (;;) {
		HAL_GPIO_TogglePin(LD1_GPIO_Port, LD1_Pin); // adapte si tu veux une autre LED
		osDelay(500);
	}
  /* USER CODE END StartHeartBeatTask */
}

/**
  * @brief  Period elapsed callback in non blocking mode
  * @note   This function is called  when TIM1 interrupt took place, inside
  * HAL_TIM_IRQHandler(). It makes a direct call to HAL_IncTick() to increment
  * a global variable "uwTick" used as application time base.
  * @param  htim : TIM handle
  * @retval None
  */
void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim)
{
  /* USER CODE BEGIN Callback 0 */
  /* USER CODE END Callback 0 */
  if (htim->Instance == TIM1)
  {
    HAL_IncTick();
  }
  /* USER CODE BEGIN Callback 1 */
  /* USER CODE END Callback 1 */
}

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* USER CODE END Error_Handler_Debug */
}
#ifdef USE_FULL_ASSERT
/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t *file, uint32_t line)
{
  /* USER CODE BEGIN 6 */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */
