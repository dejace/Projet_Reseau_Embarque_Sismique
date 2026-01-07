/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  *
  * Copyright (c) 2025 STMicroelectronics.
  * All rights reserved.
  *
  * This software is licensed under terms that can be found in the LICENSE file
  * in the root directory of this software component.
  * If no LICENSE file comes with this software, it is provided AS-IS.
  *
  ******************************************************************************
  */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "cmsis_os.h"
#include "lwip.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
#include "lwip/udp.h"
#include "lwip/pbuf.h"
#include "lwip/ip_addr.h"
#include "lwip/tcp.h"

#include <stdio.h>
#include <string.h>
#include <math.h>
#include <time.h>

#include <stdarg.h>

/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */
typedef struct {
    char text[256];
} UartMsg;


/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */
#define PRESENCE_PORT 12345 // (broadcast UDP)
#define WINDOW_SIZE 100     // Taille de la fenêtre pour le calcul du RMS
#define SEISMIC_THRESHOLD 0.3f // Seuil de détection sismique
#define NTP_MAX_RETRIES 10
#define ADC_THRESHOLD_VOLTAGE  2500
/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
DMA_HandleTypeDef hdma_adc1;
I2C_HandleTypeDef hi2c1;
RTC_HandleTypeDef hrtc;
SPI_HandleTypeDef hspi2;
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
volatile uint8_t system_is_running = 0;
/* -------------------------------------------------------------------------- */
/* GESTION DYNAMIQUE DES VOISINS                            */
/* -------------------------------------------------------------------------- */
#define MAX_NEIGHBORS 10

typedef struct {
    ip_addr_t ip;           // L'adresse IP
    uint32_t last_seen;     // Timestamp (tick) pour savoir si le noeud est vivant
    uint8_t active;         // 1 = présent, 0 = vide
} NeighborNode;

NeighborNode dynamic_node_list[MAX_NEIGHBORS];
osMutexId nodeMutexHandle; // Pour protéger la liste (UDP écrit, TCP lit)

static struct udp_pcb *presence_tx_pcb = NULL; //udp listener
static struct udp_pcb *presence_rx_pcb = NULL; // UDP RX listener


#define UART_QUEUE_LEN 64

static UartMsg uartMsgPool[UART_QUEUE_LEN];
static uint8_t uartMsgPoolIndex = 0;


/* -------------------------------------------------------------------------- */
/*                  THREADS & BUFFERS LIES AUX CAPTEURS                       */
/* -------------------------------------------------------------------------- */

/* Handle de la tâche présence réseau (Broadcast UDP) */
osThreadId presenceTaskHandle;

/* Buffer contenant les 3 valeurs ADC brutes (X, Y, Z) */
uint16_t adc_raw[3];
struct udp_pcb *ntp_pcb = NULL;

/* -------------------------------------------------------------------------- */
/*                           VARIABLES SISMIQUES                              */
/* -------------------------------------------------------------------------- */

/* Handle de la tâche sismique (calcul RMS + détection) */
osThreadId seismicTaskHandle;

/* Valeurs RMS calculées (niveau d'énergie par axe) */
float rms_x = 0, rms_y = 0, rms_z = 0;

/* Buffers circulaires sur 1 seconde (100 échantillons) pour RMS */
float buf_x[WINDOW_SIZE];
float buf_y[WINDOW_SIZE];
float buf_z[WINDOW_SIZE];

/* -------------------------------------------------------------------------- */
/*                       DEFINITIONS FRAM & RTC I2C                           */
/* -------------------------------------------------------------------------- */

/* Adresse I2C du module RTC (type DS1307 / BQ32000) */
#define RTC_ADDR 0xD0

/* Commandes SPI pour contrôle de la mémoire FRAM */
#define FRAM_WREN        0x06   // Enable Write
#define FRAM_WRITE       0x02   // Ecriture séquentielle
#define FRAM_READ        0x03   // Lecture séquentielle

//voisin
#define FRAM_LOCAL_EVENT_ADDR     0x0000
#define FRAM_NEIGHBOR_BASE_ADDR   0x0100
#define FRAM_NEIGHBOR_EVENT_SIZE   (sizeof(NeighborEvent))


/* Structure enregistrée dans la FRAM pour mémoriser un séisme */
typedef struct {
    uint8_t year;
    uint8_t month;
    uint8_t day;
    uint8_t hour;
    uint8_t min;
    uint8_t sec;
    float intensity;
} SeismicEvent;

/* --- Événement reçu d’un voisin --- */
typedef struct {
    uint8_t neighbor_id;   // index du slot (0,1,2)
    uint8_t source_ip;     // <--- AJOUT : On stocke la fin de l'IP (ex: 177)
    uint8_t year;
    uint8_t month;
    uint8_t day;
    uint8_t hour;
    uint8_t min;
    uint8_t sec;
    float intensity;
} NeighborEvent;

volatile uint8_t my_alert_status = 0;
volatile uint8_t neighbor_alert_status = 0;

/* -------------------------------------------------------------------------- */
/*                    CONFIGURATION NTP (Synchronisation RTC)                 */
/* -------------------------------------------------------------------------- */
/* Paramètres standard du protocole NTP */
#define NTP_PORT 123
#define NTP_MSG_LEN 48
#define NTP_TIMESTAMP_DELTA 2208988800u   // Conversion NTP → UNIX
#define TIMEZONE_OFFSET 1                 // UTC+1

/* État de synchronisation :
 *   0 → RTC pas encore mis à l'heure
 *   1 → Heure synchronisée
 */
volatile uint8_t ntp_synced = 0;

/* -------------------------------------------------------------------------- */
/* -------------------------------------------------------------------------- */
/* NOUVELLE GESTION MEMOIRE (HISTORIQUE)                                      */
/* -------------------------------------------------------------------------- */
#define HISTORY_DEPTH 10
#define MAX_TRACKED_NEIGHBORS 5 // On suit jusqu'à 5 voisins distincts

// 1. Structure pour l'historique LOCAL en RAM (Ajout Année/Mois/Jour)
typedef struct {
    float max_rms;
    uint8_t y, mo, d, h, m, s; // Date complète
} LocalHistoryItem;

LocalHistoryItem local_history[HISTORY_DEPTH];
uint8_t local_hist_idx = 0;

// 2. Gestion FRAM VOISINS
#define FRAM_NEIGHBOR_BLOCK_SIZE  (sizeof(NeighborEvent) * HISTORY_DEPTH)

// Index d'écriture pour chaque slot (5 slots maintenant)
uint8_t neighbor_fram_idx[MAX_TRACKED_NEIGHBORS] = {0};
uint8_t neighbor_ip_map[MAX_TRACKED_NEIGHBORS] = {0};
/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_DMA_Init(void);
static void MX_USART3_UART_Init(void);
static void MX_RTC_Init(void);
static void MX_ADC1_Init(void);
static void MX_TIM2_Init(void);
static void MX_I2C1_Init(void);
static void MX_SPI2_Init(void);
void StartDefaultTask(void const * argument);
void LogMessageTask(void const * argument);
void StartClientTask(void const * argument);
void StartServerTask(void const * argument);
void StartHeartBeatTask(void const * argument);

/* USER CODE BEGIN PFP */
void Net_ComputeBroadcastIP(ip_addr_t *dest);
void Time_FormatIso8601(char *buf, size_t len);

typedef struct {
    uint8_t year;
    uint8_t month;
    uint8_t day;
    uint8_t hour;
    uint8_t min;
    uint8_t sec;
} RTC_DateTime;

void DrvRtc_SetDateTime(uint8_t year, uint8_t month, uint8_t day,
                     uint8_t hour, uint8_t min, uint8_t sec);

void DrvRtc_GetDateTime(RTC_DateTime *dt);

/* -------------------------------------------------------------------------- */
/*                     PROTOTYPES — TÂCHES FREE RTOS                          */
/* -------------------------------------------------------------------------- */

/* Tâche de présence réseau : envoie périodiquement un broadcast UDP */
void StartPresenceTask(void const * argument);

/* Fonction qui fabrique et envoie le JSON "presence" */
void send_presence_broadcast(void);

/* Tâche principale du module sismique :
   - attend les échantillons ADC via sémaphore
   - calcule RMS
   - détecte les secousses
*/
void StartSeismicTask(void const * argument);

/* -------------------------------------------------------------------------- */
/*                       PROTOTYPES — SERVEUR TCP                             */
/* -------------------------------------------------------------------------- */

/* Initialise le serveur : bind + listen */
void tcp_server_init(void);

/* Callback : un client se connecte au serveur */
err_t tcp_server_accept(void *arg, struct tcp_pcb *newpcb, err_t err);

/* Callback : le serveur reçoit un message (ex: data_request JSON) */
err_t tcp_server_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);

/* -------------------------------------------------------------------------- */
/*                       PROTOTYPES — CLIENT TCP                              */
/* -------------------------------------------------------------------------- */

/* Fonction qui initie une connexion TCP vers une IP en particulier */
void send_data_request_tcp(const char *ip);

/* Callback : connexion réussie → on envoie un JSON data_request */
err_t tcp_client_connected(void *arg, struct tcp_pcb *tpcb, err_t err);

/* Callback : réception de la réponse data_response d’un voisin */
err_t tcp_client_recv_response(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err);

/* -------------------------------------------------------------------------- */
/*               OBJETS FREE RTOS (sémaphore + mutex)                         */
/* -------------------------------------------------------------------------- */

/* Sémaphore libéré par l'interruption ADC → réveille la tâche sismique */
osSemaphoreId adcReadySemHandle;

/* Mutex protégeant l'accès aux valeurs RMS partagées */
osMutexId dataMutexHandle;
osMutexId rtcMutexHandle; // 💡 A RAJOUTER

/* -------------------------------------------------------------------------- */
/*                          PROTOTYPES — RTC (I2C)                            */
/* -------------------------------------------------------------------------- */

/* Conversion utilitaires (le RTC utilise du BCD) */
uint8_t Rtc_DecToBcd(int val);
int Rtc_BcdToDec(uint8_t val);

/* -------------------------------------------------------------------------- */
/*                     PROTOTYPES — FRAM (SPI)                                */
/* -------------------------------------------------------------------------- */

void FRAM_Write(uint32_t addr, uint8_t *pData, uint16_t size);
void FRAM_Read(uint32_t addr, uint8_t *pData, uint16_t size);

/* -------------------------------------------------------------------------- */
/*                      PROTOTYPES — NTP (UDP)                                */
/* -------------------------------------------------------------------------- */

/* Callback appelée quand un paquet NTP arrive (réponse du serveur) */
void ntp_recv_callback(void *arg,
                       struct udp_pcb *pcb,
                       struct pbuf *p,
                       const ip_addr_t *addr,
                       u16_t port);

/* --- Réception présence UDP --- */
void presence_recv_cb(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                      const ip_addr_t *addr, u16_t port);

//gatekeeper

void App_LogPrintf(const char *fmt, ...);

/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */

void App_LogPrintf(const char *fmt, ...)
{
    UartMsg *m;
    // On utilise le Mutex pour protéger l'accès mémoire
    osMutexWait(uartMutexHandle, osWaitForever);

    m = &uartMsgPool[uartMsgPoolIndex];
    uartMsgPoolIndex = (uartMsgPoolIndex + 1) % UART_QUEUE_LEN;

    va_list args;
    va_start(args, fmt);
    vsnprintf(m->text, sizeof(m->text), fmt, args);
    va_end(args);

    osMutexRelease(uartMutexHandle);

    // Timeout à 0 : Si la queue est pleine, on jette le message au lieu de faire planter le CPU
    osMessagePut(messageQueueHandle, (uint32_t)m, 0);
}

void Net_ComputeBroadcastIP(ip_addr_t *dest)
{
    extern struct netif gnetif;

    ip4_addr_t ip   = *netif_ip4_addr(&gnetif);
    ip4_addr_t mask = *netif_ip4_netmask(&gnetif);

    ip4_addr_t bc;
    bc.addr = (ip.addr & mask.addr) | (~mask.addr);

    ip_addr_copy_from_ip4(*dest, bc);
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
  MX_I2C1_Init();
  MX_SPI2_Init();
  /* USER CODE BEGIN 2 */
  // 💡 Démarrage du Timer qui cadence l'ADC (pour avoir 100Hz précis)
  HAL_TIM_Base_Start(&htim2);
  // 💡 Démarrage de l'ADC en mode DMA Circulaire.
  // Le CPU n'a rien à faire, le DMA remplit le tableau 'adc_raw' tout seul en arrière-plan.
  HAL_ADC_Start_DMA(&hadc1, (uint32_t*)adc_raw, 3);
  /* USER CODE END 2 */

  /* Create the mutex(es) */
  /* definition and creation of uartMutex */
  osMutexDef(uartMutex);
  uartMutexHandle = osMutexCreate(osMutex(uartMutex));

  /* USER CODE BEGIN RTOS_MUTEX */
  /* add mutexes, ... */
  osMutexDef(dataMutex);
  dataMutexHandle = osMutexCreate(osMutex(dataMutex));
  osMutexDef(rtcMutex);
  rtcMutexHandle = osMutexCreate(osMutex(rtcMutex));

  // Dans le main, avec les autres mutex :
  osMutexDef(nodeMutex);
  nodeMutexHandle = osMutexCreate(osMutex(nodeMutex));
  /* USER CODE END RTOS_MUTEX */

  /* USER CODE BEGIN RTOS_SEMAPHORES */
  /* add semaphores, ... */


  /* definition and creation of adcReadySem */
  osSemaphoreDef(adcReadySem);
  adcReadySemHandle = osSemaphoreCreate(osSemaphore(adcReadySem), 1);
  osSemaphoreWait(adcReadySemHandle, 0);
  /* USER CODE END RTOS_SEMAPHORES */

  /* USER CODE BEGIN RTOS_TIMERS */
  /* start timers, add new ones, ... */

  /* USER CODE END RTOS_TIMERS */

  /* Create the queue(s) */
  /* definition and creation of messageQueue */
  osMessageQDef(messageQueue, 64, uint32_t);
  messageQueueHandle = osMessageCreate(osMessageQ(messageQueue), NULL);

  /* USER CODE BEGIN RTOS_QUEUES */
  /* add queues, ... */
  /* USER CODE END RTOS_QUEUES */

  /* Create the thread(s) */
  /* definition and creation of defaultTask */
  osThreadDef(defaultTask, StartDefaultTask, osPriorityNormal, 0, 2048);
  defaultTaskHandle = osThreadCreate(osThread(defaultTask), NULL);

  /* definition and creation of logMessageTask */
  osThreadDef(logMessageTask, LogMessageTask, osPriorityNormal, 0, 2048);
  logMessageTaskHandle = osThreadCreate(osThread(logMessageTask), NULL);

  /* definition and creation of clientTask */
  osThreadDef(clientTask, StartClientTask, osPriorityBelowNormal, 0, 2048);
  clientTaskHandle = osThreadCreate(osThread(clientTask), NULL);

  /* definition and creation of serverTask */
  osThreadDef(serverTask, StartServerTask, osPriorityBelowNormal, 0, 2048);
  serverTaskHandle = osThreadCreate(osThread(serverTask), NULL);

  /* definition and creation of heartBeatTask */
  osThreadDef(heartBeatTask, StartHeartBeatTask, osPriorityIdle, 0, 2048);
  heartBeatTaskHandle = osThreadCreate(osThread(heartBeatTask), NULL);

  /* USER CODE BEGIN RTOS_THREADS */
  /* definition and creation of presenceTask */
  // 💡 Tâche Présence : Envoie un message UDP "Je suis là" à tout le monde
  osThreadDef(presenceTask, StartPresenceTask, osPriorityBelowNormal, 0, 2048);
  presenceTaskHandle = osThreadCreate(osThread(presenceTask), NULL);

  /* add threads, ... */


  /* definition and creation of seismicTask */
  // 💡 Tâche Sismique : Priorité ÉLEVÉE car calcul critique en temps réel
  osThreadDef(seismicTask, StartSeismicTask, osPriorityAboveNormal, 0, 2048);
  seismicTaskHandle = osThreadCreate(osThread(seismicTask), NULL);

  /*  IMPORTANT : tout suspendre au début */
  //  Au démarrage, on met tout en pause Seule la tâche par défaut tourne
  // pour attendre l'appui sur le bouton bleu.
  osThreadSuspend(heartBeatTaskHandle);
  osThreadSuspend(presenceTaskHandle);
  //osThreadSuspend(logMessageTaskHandle);
  osThreadSuspend(seismicTaskHandle);
  osThreadSuspend(clientTaskHandle);
  /* USER CODE END RTOS_THREADS */

  /* Start scheduler */
  osKernelStart();

  /* We should never get here as control is now taken by the scheduler */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
  while (1)
  {
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
  }
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
  hadc1.Init.EOCSelection = ADC_EOC_SEQ_CONV;
  if (HAL_ADC_Init(&hadc1) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_4;
  sConfig.Rank = ADC_REGULAR_RANK_1;
  sConfig.SamplingTime = ADC_SAMPLETIME_15CYCLES;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_5;
  sConfig.Rank = ADC_REGULAR_RANK_2;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_6;
  sConfig.Rank = ADC_REGULAR_RANK_3;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN ADC1_Init 2 */

  /* USER CODE END ADC1_Init 2 */

}

/**
  * @brief I2C1 Initialization Function
  * @param None
  * @retval None
  */
static void MX_I2C1_Init(void)
{

  /* USER CODE BEGIN I2C1_Init 0 */

  /* USER CODE END I2C1_Init 0 */

  /* USER CODE BEGIN I2C1_Init 1 */

  /* USER CODE END I2C1_Init 1 */
  hi2c1.Instance = I2C1;
  hi2c1.Init.Timing = 0x40000A0B;
  hi2c1.Init.OwnAddress1 = 0;
  hi2c1.Init.AddressingMode = I2C_ADDRESSINGMODE_7BIT;
  hi2c1.Init.DualAddressMode = I2C_DUALADDRESS_DISABLE;
  hi2c1.Init.OwnAddress2 = 0;
  hi2c1.Init.OwnAddress2Masks = I2C_OA2_NOMASK;
  hi2c1.Init.GeneralCallMode = I2C_GENERALCALL_DISABLE;
  hi2c1.Init.NoStretchMode = I2C_NOSTRETCH_DISABLE;
  if (HAL_I2C_Init(&hi2c1) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure Analogue filter
  */
  if (HAL_I2CEx_ConfigAnalogFilter(&hi2c1, I2C_ANALOGFILTER_ENABLE) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure Digital filter
  */
  if (HAL_I2CEx_ConfigDigitalFilter(&hi2c1, 0) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN I2C1_Init 2 */

  /* USER CODE END I2C1_Init 2 */

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
  * @brief SPI2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_SPI2_Init(void)
{

  /* USER CODE BEGIN SPI2_Init 0 */

  /* USER CODE END SPI2_Init 0 */

  /* USER CODE BEGIN SPI2_Init 1 */

  /* USER CODE END SPI2_Init 1 */
  /* SPI2 parameter configuration*/
  hspi2.Instance = SPI2;
  hspi2.Init.Mode = SPI_MODE_MASTER;
  hspi2.Init.Direction = SPI_DIRECTION_2LINES;
  hspi2.Init.DataSize = SPI_DATASIZE_8BIT;
  hspi2.Init.CLKPolarity = SPI_POLARITY_LOW;
  hspi2.Init.CLKPhase = SPI_PHASE_1EDGE;
  hspi2.Init.NSS = SPI_NSS_SOFT;
  hspi2.Init.BaudRatePrescaler = SPI_BAUDRATEPRESCALER_2;
  hspi2.Init.FirstBit = SPI_FIRSTBIT_MSB;
  hspi2.Init.TIMode = SPI_TIMODE_DISABLE;
  hspi2.Init.CRCCalculation = SPI_CRCCALCULATION_DISABLE;
  hspi2.Init.CRCPolynomial = 7;
  hspi2.Init.CRCLength = SPI_CRC_LENGTH_DATASIZE;
  hspi2.Init.NSSPMode = SPI_NSS_PULSE_ENABLE;
  if (HAL_SPI_Init(&hspi2) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN SPI2_Init 2 */

  /* USER CODE END SPI2_Init 2 */

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
  HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_SET);

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

  /*Configure GPIO pin : FRAM_CS_Pin */
  GPIO_InitStruct.Pin = FRAM_CS_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(FRAM_CS_GPIO_Port, &GPIO_InitStruct);

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



/**
  * @brief Tâche pour la découverte réseau (Protocole de présence)
  * @note  Envoie périodiquement un broadcast UDP pour dire "Je suis là"
  * Cette tâche envoie régulièrement un message JSON "presence" afin
  * de signaler l’existence du nœud sur le réseau local.
  */
void StartPresenceTask(void const * argument)
{

    /* Attendre que la pile réseau LwIP soit opérationnelle */
    extern struct netif gnetif;

    // On boucle tant que :
    //   - la carte n'a pas obtenu d'adresse IP
    //   - le câble Ethernet n'est pas connecté
    while (!netif_is_up(&gnetif))
    {
        osDelay(100);
    }

    presence_tx_pcb = udp_new_ip_type(IPADDR_TYPE_V4);
    if (!presence_tx_pcb)
    {
    	App_LogPrintf("❌ presence TX pcb alloc failed\r\n");
        vTaskDelete(NULL);
    }

    presence_tx_pcb->so_options |= SOF_BROADCAST;
    udp_bind(presence_tx_pcb, IP_ADDR_ANY, 0);
    ip_set_option(presence_tx_pcb, SOF_BROADCAST);

    App_LogPrintf("UDP presence TX ready\r\n");

    /* Boucle principale : envoi périodique du broadcast */
    for (;;)
    {
        send_presence_broadcast();  // Envoi JSON presence
        osDelay(10000);             // 10 secondes entre deux annonces
    }
}

/**
  * @brief Fonction d'envoi du message UDP Broadcast
  * @note  Crée un socket UDP temporaire, envoie le JSON, puis ferme le socket.
  *
  * Étapes :
  *   1. Création d’un PCB UDP (socket LwIP)
  *   2. Activation du mode broadcast
  *   3. Construction dynamique du JSON (IP réelle incluse)
  *   4. Allocation d’un pbuf et copie des données
  *   5. Envoi du paquet sur l’adresse 192.168.129.255
  *   6. Libération du buffer et fermeture du PCB
  */

void send_presence_broadcast(void)
{
	if (!presence_tx_pcb)
	    return;

    //struct udp_pcb *pcb;
    struct pbuf *p;
    ip_addr_t dest_ip;
    Net_ComputeBroadcastIP(&dest_ip);

    extern struct netif gnetif;
    /* ---------------------------------------------------------------------- */
    /*                  Construction du message JSON "presence"               */
    /* ---------------------------------------------------------------------- */
    char json[256];

    // Récupération dynamique de l'adresse IP actuelle via LwIP
    //extern struct netif gnetif;
    char *device_ip = ipaddr_ntoa(&gnetif.ip_addr);

    char ts[32];
    Time_FormatIso8601(ts, sizeof(ts));

    snprintf(json, sizeof(json),
     "{ \"type\": \"presence\", \"id\": \"nucleo-11\", \"ip\": \"%s\", "
     "\"timestamp\": \"%s\" }",
     device_ip, ts);


    /* ---------------------------------------------------------------------- */
    /*               Allocation d’un pbuf contenant le JSON                   */
    /* ---------------------------------------------------------------------- */

    p = pbuf_alloc(PBUF_TRANSPORT, strlen(json), PBUF_RAM);
    if (!p)
    {
        //udp_remove(pcb);   // Éviter fuite mémoire
        return;
    }

    /* Copie du JSON dans le buffer transport (payload LwIP) */
    memcpy(p->payload, json, strlen(json));

    /* 4. Envoi du message UDP en broadcast */
    err_t err = udp_sendto(presence_tx_pcb, p, &dest_ip, PRESENCE_PORT);
    if (err == ERR_OK)
    {
    	App_LogPrintf("UDP PRESENCE SENT => %s\r\n", json);
    }
    else
    {
    	App_LogPrintf("UDP PRESENCE SEND ERROR (%d)\r\n", err);
    }


    /* ---------------------------------------------------------------------- */
    /*                          Libérations mémoire                           */
    /* ---------------------------------------------------------------------- */

    pbuf_free(p);    // Libération buffer
}

/**
  * @brief Callback déclenchée lorsque le DMA termine un transfert ADC.
  *
  * Cette fonction est appelée par le HAL lorsque :
  *   - l’ADC1 a terminé la conversion des 3 canaux,
  *   - et que le DMA a copié les valeurs dans adc_raw[].
  *
  * Rôle :
  *   ✔ Débloquer la tâche sismique (StartSeismicTask) via un sémaphore
  *   ✔ Indiquer visuellement l’acquisition (clignotement LED2)
  *
  * Note :
  *   Aucun calcul ne doit être fait ici → fonction courte et réactive.
  */
void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef *hadc)
{
    /* Vérifie que l'interruption provient bien de l'ADC1 */
    if (hadc->Instance == ADC1)
    {
        /* Débloque la tâche sismique pour traiter une nouvelle mesure */
        osSemaphoreRelease(adcReadySemHandle);

        /* Clignotement LED2 = indicateur visuel des acquisitions ADC */
        HAL_GPIO_TogglePin(LD2_GPIO_Port, LD2_Pin);
    }
}

/**
  * @brief Tâche de traitement du signal sismique
  * @note  Lit les valeurs brutes, filtre (moyenne) et calcule l'énergie (RMS)
  * Fonctionnement :
  *   1️ Attente d’une nouvelle mesure ADC via sémaphore (DMA → Callback)
  *   2️ Mise à jour des buffers (fenêtre glissante de 100 échantillons)
  *   3️ Calcul de la moyenne puis du RMS pour X/Y/Z
  *   4️ Détection locale si RMS dépasse un SEUIL
  *   5️ Enregistrement horodaté dans la FRAM toutes les 2 secondes
  *   6️ Flash mémoire RAM : stockage des 10 derniers pics locaux
  *   7️ Log UART horodaté
  *   8️ Alerte collective si NOEUD + VOISIN détectent un tremblement
  */
void StartSeismicTask(void const * argument)
{
    /* Initialisation : vider les buffers circulaires RMS */
    memset(buf_x, 0, sizeof(buf_x));
    memset(buf_y, 0, sizeof(buf_y));
    memset(buf_z, 0, sizeof(buf_z));

    int buffer_idx = 0;
    uint32_t last_tremor_time = 0;
    uint32_t last_print_time = 0;
    uint32_t last_save_time  = 0;


    // Ajout d'un timer pour ne pas remplir l'historique RAM trop vite
    uint32_t last_ram_update = 0;
    char msg[100];


    for (;;)
    {
        /* 1️⃣ Attente ADC */
        osSemaphoreWait(adcReadySemHandle, osWaitForever);

        /* 2️⃣ Acquisition des valeurs brutes */
        float raw_x = adc_raw[0];
        float raw_y = adc_raw[1];
        float raw_z = adc_raw[2];

        /* Mise à jour buffers pour RMS */
        buf_x[buffer_idx] = raw_x;
        buf_y[buffer_idx] = raw_y;
        buf_z[buffer_idx] = raw_z;

        // A. Calcul de la MOYENNE
        float mean_x = 0, mean_y = 0, mean_z = 0;
        for (int i = 0; i < WINDOW_SIZE; i++) {
            mean_x += buf_x[i]; mean_y += buf_y[i]; mean_z += buf_z[i];
        }
        mean_x /= WINDOW_SIZE; mean_y /= WINDOW_SIZE; mean_z /= WINDOW_SIZE;

        // B. Calcul de la VARIANCE
        float var_x = 0, var_y = 0, var_z = 0;
        for (int i = 0; i < WINDOW_SIZE; i++) {
            var_x += powf(buf_x[i] - mean_x, 2);
            var_y += powf(buf_y[i] - mean_y, 2);
            var_z += powf(buf_z[i] - mean_z, 2);
        }

        // C. Calcul du RMS Brut converti en Volts
        float calc_rms_x = sqrtf(var_x / WINDOW_SIZE);
        float calc_rms_y = sqrtf(var_y / WINDOW_SIZE);
        float calc_rms_z = sqrtf(var_z / WINDOW_SIZE);

        calc_rms_x = (calc_rms_x * 3.3f) / 4095.0f;
        calc_rms_y = (calc_rms_y * 3.3f) / 4095.0f;
        calc_rms_z = (calc_rms_z * 3.3f) / 4095.0f;

        /* Mise à jour globale pour le serveur TCP */
        osMutexWait(dataMutexHandle, osWaitForever);
        rms_x = calc_rms_x; rms_y = calc_rms_y; rms_z = calc_rms_z;
        osMutexRelease(dataMutexHandle);

        /* -------------------------------------------------------------- */
        /* 4️⃣ DÉTECTION ET STOCKAGE                                       */
        /* -------------------------------------------------------------- */

        if (raw_x > ADC_THRESHOLD_VOLTAGE ||
            raw_y > ADC_THRESHOLD_VOLTAGE ||
            raw_z > ADC_THRESHOLD_VOLTAGE)
        {
            my_alert_status = 1;
            last_tremor_time = HAL_GetTick();

            // --- CORRECTION : CALCUL DU MAX IMMÉDIAT ---
            float max_rms = calc_rms_x;
            if (calc_rms_y > max_rms) max_rms = calc_rms_y;
            if (calc_rms_z > max_rms) max_rms = calc_rms_z;
            // On limite à une écriture tous les 200ms pour voir l'évolution
            // --- 1. Stockage en RAM (Historique complet avec DATE + HEURE) ---
                        if (HAL_GetTick() - last_ram_update > 200)
                        {
                            RTC_DateTime dt_now;
                            DrvRtc_GetDateTime(&dt_now);

                            // Enregistrement complet
                            local_history[local_hist_idx].max_rms = max_rms;
                            local_history[local_hist_idx].y  = dt_now.year;
                            local_history[local_hist_idx].mo = dt_now.month;
                            local_history[local_hist_idx].d  = dt_now.day;
                            local_history[local_hist_idx].h  = dt_now.hour;
                            local_history[local_hist_idx].m  = dt_now.min;
                            local_history[local_hist_idx].s  = dt_now.sec;

                            // Incrément circulaire (0 -> 9 puis retour à 0)
                            local_hist_idx = (local_hist_idx + 1) % HISTORY_DEPTH;

                            last_ram_update = HAL_GetTick();
                        }

            // --- 2. Log UART (toutes les 500ms) ---
            if (HAL_GetTick() - last_print_time > 500)
            {
                // Conversion inverse pour affichage debug tension brute
                float vol_x = (raw_x * 3.3f) / 4095.0f;
                RTC_DateTime dt;
                DrvRtc_GetDateTime(&dt);

                sprintf(msg, "[%02d:%02d:%02d] SEISME ! RMS: %.2fV (Pic Brute: %.2fV)\r\n",
                        dt.hour, dt.min, dt.sec, max_rms, vol_x);
                App_LogPrintf("%s", msg);
                last_print_time = HAL_GetTick();
            }

            // --- 3. Stockage FRAM (Lent : toutes les 2s) ---
            if (HAL_GetTick() - last_save_time > 2000)
            {
                RTC_DateTime dt;
                DrvRtc_GetDateTime(&dt);

                SeismicEvent evt = {
                    dt.year, dt.month, dt.day, dt.hour, dt.min, dt.sec,
                    max_rms
                };

                FRAM_Write(FRAM_LOCAL_EVENT_ADDR, (uint8_t*)&evt, sizeof(evt));
                HAL_GPIO_WritePin(LD3_GPIO_Port, LD3_Pin, GPIO_PIN_SET);

                App_LogPrintf("Evenement local sauvegarde en FRAM.\r\n");
                last_save_time = HAL_GetTick();
            }
        }
        else
        {
            // Extinction alerte après 3s de calme
            if (HAL_GetTick() - last_tremor_time > 6000)
            {
                if (my_alert_status == 1)
                {
                    my_alert_status = 0;
                    HAL_GPIO_WritePin(LD3_GPIO_Port, LD3_Pin, GPIO_PIN_RESET);
                    App_LogPrintf("Fin de l'alerte locale.\r\n");
                }
            }
        }

        // 7. Alerte Collective
        if (my_alert_status == 1 && neighbor_alert_status == 1)
        {
            HAL_GPIO_TogglePin(LD3_GPIO_Port, LD3_Pin);
        }

        buffer_idx = (buffer_idx + 1) % WINDOW_SIZE;
    }
}

static struct tcp_pcb *server_pcb;

/**
  * @brief Initialisation du serveur TCP
  * @note  Ouvre le port 12345 en écoute
  *   1️ Création d’un PCB TCP (socket LwIP)
  *   2️ bind → association du port TCP 12345 au PCB
  *   3️ listen → passage du serveur en mode écoute
  *   4️ accept callback → fonction déclenchée lorsqu’un client se connecte
  */
void tcp_server_init(void)
{
    /* 1️⃣ Création d’un nouveau PCB TCP */
    server_pcb = tcp_new();
    if (server_pcb == NULL)
    {
        // Impossible de créer le PCB TCP
        return;
    }

    /* 2️⃣ Bind : attacher le PCB au port TCP 12345 */
    tcp_bind(server_pcb, IP_ADDR_ANY, 12345);

    /* 3️⃣ Passage en mode écoute — le PCB devient un serveur */
    server_pcb = tcp_listen(server_pcb);

    /* 4️⃣ Définir la fonction callback appelée lors d’une nouvelle connexion */
    tcp_accept(server_pcb, tcp_server_accept);
}

/* 💡 Callback appelée quand un nouveau client se connecte au serveur
 * * Paramètres :
  *   - newpcb : PCB dédié à la nouvelle connexion client
  *   - err    : état de la connexion (généralement ERR_OK)
  *
  * Rôle :
  *   ✔ Log UART → affiche l'adresse IP du client
  *   ✔ Associe au client une routine de réception (tcp_server_recv)
  *
  * Remarque :
  *   Une connexion → un PCB dédié. Le serveur reste disponible pour d'autres clients.
  */
err_t tcp_server_accept(void *arg, struct tcp_pcb *newpcb, err_t err)
{
    /* En cas d’erreur de connexion, on refuse immédiatement */
	//* --- AJOUT : Si le système est en pause, on refuse la connexion --- */
	if (system_is_running == 0) {
	    tcp_abort(newpcb);
	    return ERR_ABRT;
	}
	    /* ------------------------------------------------------------------ */
	    /* En cas d’erreur de connexion, on refuse immédiatement */
	    if (err != ERR_OK || newpcb == NULL)
	    {
	        return ERR_VAL;
	    }
	    /* ------------------------- LOG DE CONNEXION -------------------------- */
	    App_LogPrintf("📥 Client connecté depuis %s\r\n", ipaddr_ntoa(&newpcb->remote_ip));

    /* ----------------------------------------------------------------------
     * Associer une fonction de réception TCP dédiée à cette connexion.
     * → À chaque fois que le client envoie un paquet,
     *   tcp_server_recv() sera appelée.
     * ---------------------------------------------------------------------- */
    tcp_recv(newpcb, tcp_server_recv);

    return ERR_OK;
}
/*
 * Fonction appelée automatiquement lorsqu’un client (voisin)
 * envoie des données à TON serveur TCP.
 */
err_t tcp_server_recv(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err)
{
    // 1. Vérification standard (Connexion coupée ou erreur)
    if (err != ERR_OK || p == NULL) {
        if (p) pbuf_free(p);
        tcp_close(tpcb);
        return ERR_OK;
    }

    // 2. On "consomme" le paquet reçu (on dit à LwIP qu'on l'a lu)
    tcp_recved(tpcb, p->tot_len);

    // On libère le buffer d'entrée immédiatement, on sait que c'est une demande
    pbuf_free(p);

    // 3. Récupération des données locales (RMS actuel)
    float tx_x, tx_y, tx_z;
    osMutexWait(dataMutexHandle, osWaitForever);
    tx_x = rms_x; tx_y = rms_y; tx_z = rms_z;
    osMutexRelease(dataMutexHandle);

    // 4. Préparation du Timestamp (Format "Ahmed" avec les espaces)
    // 4. Préparation du Timestamp ISO (sans espaces)
    char ts_str[32];
    Time_FormatIso8601(ts_str, sizeof(ts_str));

    // 5. Détermination CLAIRE du statut (Alerte ou Normal)
    // C'est la ligne la plus importante : elle regarde ta variable globale
    const char *status_str = (my_alert_status == 1) ? "alert" : "normal";

    // 6. Construction de la RÉPONSE JSON
    char response[256];
    snprintf(response, sizeof(response),
     "{ \"type\": \"data_response\", \"id\": \"nucleo-11\", "
     "\"timestamp\": \"%s\", "
     "\"acceleration\": {\"x\": %.2f, \"y\": %.2f, \"z\": %.2f}, "
     "\"status\": \"%s\" }",
     ts_str, tx_x, tx_y, tx_z, status_str);
 // <--- Ici on injecte "alert" ou "normal"

    // =================================================================
    // 🚨 AFFICHAGE UART : C'est ici que tu vérifies ce que tu envoies
    // =================================================================
    App_LogPrintf("\r\n--------------------------------------------------\r\n");
    App_LogPrintf("[TX REPONSE VERS VOISIN] >> %s\r\n", response);

    if (my_alert_status == 1) {
    	App_LogPrintf("ATTENTION : J'ENVOIE LE STATUS 'ALERT' !\r\n");
    } else {
    	App_LogPrintf("INFO : J'envoie le status 'normal'.\r\n");
    }
    App_LogPrintf("--------------------------------------------------\r\n");
    // =================================================================

    // 7. Envoi TCP (C'est ici que le message part dans le câble)
    tcp_write(tpcb, response, strlen(response), TCP_WRITE_FLAG_COPY);
    tcp_output(tpcb); // Force l'envoi immédiat

    // 8. On ferme la connexion car on a répondu
    tcp_close(tpcb);

    return ERR_OK;
}

/**
  * @brief Fonction Client TCP : Initie une connexion vers une IP
  *
  * Initialise une connexion TCP vers une carte voisine afin
  *         d'envoyer une requête JSON de type "data_request".
  *
  * Rôle :
  *   ✔ Créer un PCB client TCP
  *   ✔ Démarrer une connexion vers l'IP cible
  *   ✔ Si connexion réussie → callback tcp_client_connected()
  *   ✔ Si erreur → message UART + abort du PCB
  *
  * @param ip  Adresse IP du voisin (ex : "192.168.1.101")
  */
void send_data_request_tcp(const char *ip)
{
    /* ----------------------------------------------------------------------
     * 1) Création du PCB TCP (socket client)
     * ---------------------------------------------------------------------- */
    struct tcp_pcb *pcb = tcp_new();
    if (!pcb)
    {
    	App_LogPrintf("❌ tcp_new FAILED\r\n");
        return;
    }

    /* ----------------------------------------------------------------------
     * 2) Conversion de l’adresse IP ASCII → format LwIP
     * ---------------------------------------------------------------------- */
    ip_addr_t dest_ip;
    ipaddr_aton(ip, &dest_ip);

    /* Message UART d’information */
    App_LogPrintf("🔵 Connexion vers %s...\r\n", ip);

    /* ----------------------------------------------------------------------
     * 3) Tentative de connexion TCP
     *    - Port cible : 12345
     *    - Callback après connexion : tcp_client_connected()
     * ---------------------------------------------------------------------- */
    err_t err = tcp_connect(pcb, &dest_ip, 12345, tcp_client_connected);

    /* ----------------------------------------------------------------------
     * 4) Gestion d’erreur connexion
     * ---------------------------------------------------------------------- */
    if (err != ERR_OK)
    {
    	App_LogPrintf("❌ tcp_connect ERROR = %d\r\n", err);
        /* tcp_abort() détruit le PCB proprement (pas de fuite mémoire) */
        tcp_abort(pcb);
    }
}


// 💡 Callback appelée quand la connexion client est réussie
/*ppelée automatiquement par LwIP lorsque le client TCP arrive à
  *         se connecter au serveur voisin.
  *
  * Rôle :
  *   ✔ Vérifier que la connexion est valide
  *   ✔ Installer la fonction de réception (tcp_client_recv_response)
  *   ✔ Construire et envoyer la requête JSON "data_request"
  **/
// 💡 Callback appelée quand la connexion client est réussie
err_t tcp_client_connected(void *arg, struct tcp_pcb *tpcb, err_t err)
{
    /* ----------------------------- Vérification ---------------------------- */
    if (err != ERR_OK)
    {
        tcp_close(tpcb);  // Connexion ratée → fermeture du PCB
        return err;
    }
    /* ----------------------------------------------------------------------
     * 1) Définir la fonction qui traitera la réponse du serveur
     * ---------------------------------------------------------------------- */
    tcp_recv(tpcb, tcp_client_recv_response);

    /* ----------------------------------------------------------------------
     * 2) Construction de la requête JSON conforme aux spécifications
     * ---------------------------------------------------------------------- */
    char sendbuf[256];
    char ts[32];
    Time_FormatIso8601(ts, sizeof(ts));

    snprintf(sendbuf, sizeof(sendbuf),
     "{ \"type\": \"data_request\", \"from\": \"nucleo-11\", \"to\": \"%s\", "
     "\"timestamp\": \"%s\" }",
     ipaddr_ntoa(&tpcb->remote_ip), ts);

    // ============================================================
    // On affiche ce qu'on envoie sur l'UART
    // ============================================================
    App_LogPrintf("[TX CLIENT] << %s\r\n", sendbuf);
    // ============================================================

    /* ----------------------------------------------------------------------
     * 3) Envoi de la requête JSON vers le voisin
     * ---------------------------------------------------------------------- */
    tcp_write(tpcb, sendbuf, strlen(sendbuf), TCP_WRITE_FLAG_COPY);

    tcp_output(tpcb);

    /* ⚠️ IMPORTANT : on NE ferme PAS la connexion ici !
       La fonction tcp_client_recv_response() s'en occupera. */

    return ERR_OK;
}

/*
 * Traite le JSON envoyé par le serveur.
  *
  * Rôle :
  *   ✔ Lire et copier proprement les données reçues
  *   ✔ Extraire l’état ("status") : normal / alert
  *   ✔ Extraire les valeurs RMS x, y, z du voisin
  *   ✔ Mettre à jour l’intelligence collective (10 derniers pics)
  *   ✔ Déclencher l’alerte collective si nécessaire
  *   ✔ Fermer proprement la connexion TCP
 * */
err_t tcp_client_recv_response(void *arg, struct tcp_pcb *tpcb, struct pbuf *p, err_t err)
{
    if (err != ERR_OK || p == NULL) {
        if (p) pbuf_free(p);
        tcp_close(tpcb);
        return ERR_OK;
    }

    // Copier TOUT le message TCP (pbuf peut être chaîné)
    char buffer[256];
    uint16_t copy_len = (p->tot_len < sizeof(buffer) - 1) ? p->tot_len : (sizeof(buffer) - 1);
    pbuf_copy_partial(p, buffer, copy_len, 0);
    buffer[copy_len] = '\0';

    tcp_recved(tpcb, p->tot_len);

    App_LogPrintf("\r\n[RX CLIENT] >> %s\r\n", buffer);
    App_LogPrintf("DBG: remote=%s\r\n", ipaddr_ntoa(&tpcb->remote_ip));

    // --- IP suffix ---
    ip4_addr_t *addr_ptr = ip_2_ip4(&tpcb->remote_ip);
    uint8_t ip_suffix = ip4_addr4(addr_ptr);
    App_LogPrintf("DBG: ip_suffix=%d\r\n", ip_suffix);

    // --- Status ---
    int is_alert = (strstr(buffer, "\"status\": \"alert\"") != NULL);

    // --- Acceleration ---
    float rx_x = 0, rx_y = 0, rx_z = 0;
    char *acc_ptr = strstr(buffer, "\"acceleration\"");
    if (acc_ptr) {
        char *px = strstr(acc_ptr, "\"x\"");
        if (px) { while(*px && (*px<'0'||*px>'9') && *px!='-') px++; sscanf(px, "%f", &rx_x); }

        char *py = strstr(acc_ptr, "\"y\"");
        if (py) { while(*py && (*py<'0'||*py>'9') && *py!='-') py++; sscanf(py, "%f", &rx_y); }

        char *pz = strstr(acc_ptr, "\"z\"");
        if (pz) { while(*pz && (*pz<'0'||*pz>'9') && *pz!='-') pz++; sscanf(pz, "%f", &rx_z); }
    }

    float neighbor_max_rms = rx_x;
    if (rx_y > neighbor_max_rms) neighbor_max_rms = rx_y;
    if (rx_z > neighbor_max_rms) neighbor_max_rms = rx_z;
    App_LogPrintf("DBG: neighbor_max_rms=%.3f\r\n", neighbor_max_rms);

    // --- Timestamp ---
    int ny, nmo, nd, nh, nmin, ns;
    char *ts_ptr = strstr(buffer, "\"timestamp\"");
    if (!ts_ptr) {
    	App_LogPrintf("❌ DBG: Pas de champ timestamp\r\n");
        goto skip_neighbor_fram;
    }

    while (*ts_ptr && (*ts_ptr < '0' || *ts_ptr > '9')) ts_ptr++;

    int r = sscanf(ts_ptr, "%d-%d-%d %*c %d:%d:%d", &ny, &nmo, &nd, &nh, &nmin, &ns);
    if (r != 6) r = sscanf(ts_ptr, "%d-%d-%dT%d:%d:%d", &ny, &nmo, &nd, &nh, &nmin, &ns);

    if (r != 6) {
    	App_LogPrintf("❌ DBG: Timestamp non parsable: %s\r\n", ts_ptr);
        goto skip_neighbor_fram;
    }

    if (ny > 2000) ny -= 2000;

    App_LogPrintf("DBG: date ok y=%d mo=%d d=%d h=%d m=%d s=%d\r\n", ny,nmo,nd,nh,nmin,ns);

skip_neighbor_fram:

    if (is_alert) {
        neighbor_alert_status = 1;
        App_LogPrintf("ALERTE VOISIN (.%d) ! Force: %.2f\r\n", ip_suffix, neighbor_max_rms);
    } else {
        neighbor_alert_status = 0;
    }

    if (my_alert_status && neighbor_alert_status) {
    	App_LogPrintf("\r\n ALERTE GENERALE !\r\n");
    }

    pbuf_free(p);
    tcp_close(tpcb);
    return ERR_OK;
}


/*
 * OUTILS DE CONVERSION BCD <-> DECIMAL (utilisés par le RTC)         */
/* -------------------------------------------------------------------------- */
/**
  * @brief Convertit un entier décimal en format BCD.
  *
  * Exemple :
  *   45 décimal → 0x45 en BCD
  *
  * @param val  Valeur décimale (0–99)
  * @return     Valeur codée en BCD (Binary Coded Decimal)
 * */
// --- OUTILS CONVERSION (Le RTC parle en BCD, nous en Décimal) ---
// Exemple : 45 secondes -> 0x45 (BCD)
uint8_t Rtc_DecToBcd(int val)
{
    return (uint8_t)((val / 10 * 16) + (val % 10));
}

/**
  * @brief Convertit un octet BCD en entier décimal.
  *
  * Exemple :
  *   0x45 → 45
  *
  * @param val  Valeur en BCD
  * @return     Valeur décimale
  */
int Rtc_BcdToDec(uint8_t val)
{
    return (int)((val / 16 * 10) + (val % 16));
}

/*Programme l'heure dans le RTC.
/* -------------------------------------------------------------------------- */
/* FONCTIONS RTC SÉCURISÉES (AVEC MUTEX)                               */
/* -------------------------------------------------------------------------- */

void DrvRtc_SetDateTime(uint8_t year, uint8_t month, uint8_t day,
                     uint8_t hour, uint8_t min, uint8_t sec)
{
    uint8_t data[7];

    data[0] = Rtc_DecToBcd(sec);
    data[1] = Rtc_DecToBcd(min);
    data[2] = Rtc_DecToBcd(hour);
    data[3] = Rtc_DecToBcd(1);
    data[4] = Rtc_DecToBcd(day);
    data[5] = Rtc_DecToBcd(month);
    data[6] = Rtc_DecToBcd(year);

    // 🔒 PROTECTION I2C (INDISPENSABLE ICI AUSSI)
    osMutexWait(rtcMutexHandle, osWaitForever);

    HAL_I2C_Mem_Write(&hi2c1,
                      RTC_ADDR,
                      0x00,
                      1,
                      data,
                      7,
                      1000);

    // 🔓 LIBÉRATION
    osMutexRelease(rtcMutexHandle);
}

void DrvRtc_GetDateTime(RTC_DateTime *dt)
{
    uint8_t data[7];

    // 🔒 PROTECTION I2C
    osMutexWait(rtcMutexHandle, osWaitForever);

    HAL_I2C_Mem_Read(&hi2c1,
                     RTC_ADDR,
                     0x00,
                     1,
                     data,
                     7,
                     1000);

    // 🔓 LIBÉRATION
    osMutexRelease(rtcMutexHandle);

    dt->sec   = Rtc_BcdToDec(data[0] & 0x7F);
    dt->min   = Rtc_BcdToDec(data[1]);
    dt->hour  = Rtc_BcdToDec(data[2]);
    dt->day   = Rtc_BcdToDec(data[4]);
    dt->month = Rtc_BcdToDec(data[5]);
    dt->year  = Rtc_BcdToDec(data[6]);
}

// --- DRIVER FRAM (CY15B104Q via SPI2) ---


// Fonction interne pour activer l'écriture (WREN)
/* -------------------------------------------------------------------------- */
/*                  FRAM SPI — Commandes et opérations bas niveau             */
/* -------------------------------------------------------------------------- */
/**
  * @brief  Active le mode écriture dans la FRAM (Write Enable - WREN)
  *
  * Rôle :
  *   ✔ La FRAM refuse toute écriture tant que la commande WREN n'est pas envoyée
  *   ✔ Cette commande doit précéder **chaque écriture**
  *
  * Séquence SPI :
  *   CS ↓
  *   Envoi : 0x06 (FRAM_WREN)
  *   CS ↑
  */
void DrvFram_EnableWrite(void)
{
    uint8_t cmd = FRAM_WREN;

    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_RESET);   // CS LOW = Active
    HAL_SPI_Transmit(&hspi2, &cmd, 1, 100);                  // Envoi commande WREN
    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_SET);     // CS HIGH = Inactive
}

/* -------------------------------------------------------------------------- */
/*                      ÉCRITURE dans la FRAM (Write Operation)               */
/* -------------------------------------------------------------------------- */
/**
  * @brief  Écrit un bloc de données dans la FRAM à une adresse 24 bits.
  *
  * Séquence d’écriture SPI :
  *   1) WREN (obligatoire)
  *   2) CS ↓
  *   3) Envoi opcode WRITE (0x02)
  *   4) Envoi adresse 24 bits : A23 A22 ... A0
  *   5) Envoi des données
  *   6) CS ↑
  *
  * @param addr  Adresse 24 bits (0x000000–0x0FFFFF suivant modèle)
  * @param pData Pointeur vers les données à écrire
  * @param size  Nombre d’octets à écrire
  */
void FRAM_Write(uint32_t addr, uint8_t *pData, uint16_t size)
{
    /* 1) Autoriser l’écriture */
	DrvFram_EnableWrite();

    /* 2) Préparation du buffer commande + adresse */
    uint8_t cmd[4];
    cmd[0] = FRAM_WRITE;              // Opcode 0x02
    cmd[1] = (addr >> 16) & 0xFF;     // Adresse MSB
    cmd[2] = (addr >> 8)  & 0xFF;
    cmd[3] = addr & 0xFF;             // Adresse LSB

    /* 3) Séquence SPI d’écriture */
    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_RESET);      // CS LOW

    HAL_SPI_Transmit(&hspi2, cmd, 4, 100);                         // Commande + adresse
    HAL_SPI_Transmit(&hspi2, pData, size, 100);                    // Données

    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_SET);           // CS HIGH
}

/* -------------------------------------------------------------------------- */
/*                        LECTURE dans la FRAM (Read Operation)               */
/* -------------------------------------------------------------------------- */
/**
  * @brief  Lit un bloc d’octets depuis la FRAM.
  *
  * Séquence SPI :
  *   CS ↓
  *   Envoi opcode READ (0x03)
  *   Envoi adresse 24 bits
  *   Réception des données
  *   CS ↑
  *
  * @param addr  Adresse 24 bits à lire
  * @param pData Pointeur vers buffer de réception
  * @param size  Nombre d’octets à lire
  */
void FRAM_Read(uint32_t addr, uint8_t *pData, uint16_t size)
{
    uint8_t cmd[4];
    cmd[0] = FRAM_READ;               // Opcode 0x03
    cmd[1] = (addr >> 16) & 0xFF;
    cmd[2] = (addr >> 8)  & 0xFF;
    cmd[3] = addr & 0xFF;

    /* Séquence SPI */
    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_RESET);        // CS LOW

    HAL_SPI_Transmit(&hspi2, cmd, 4, 100);                         // Envoi commande + adresse
    HAL_SPI_Receive(&hspi2, pData, size, 100);                     // Lecture données

    HAL_GPIO_WritePin(FRAM_CS_GPIO_Port, FRAM_CS_Pin, GPIO_PIN_SET);        // CS HIGH
}
/* -------------------------------------------------------------------------- */
/*        CALLBACK NTP — Appelée lorsqu’une réponse NTP est reçue (UDP)       */
/* -------------------------------------------------------------------------- */
/**
  * @brief  Traite le paquet NTP reçu depuis le serveur de temps.
  *
  * Paquet NTP :
  *   - Taille minimale : 48 octets
  *   - Le timestamp "Transmit Timestamp" se trouve à l’offset 40
  *     → format 32 bits "Seconds since 1900"
  *
  * Rôle :
  *   ✔ Extraire la date/heure NTP (big endian)
  *   ✔ Convertir vers epoch UNIX (1970)
  *   ✔ Ajouter le fuseau horaire (Belgique = UTC+1)
  *   ✔ Mettre à jour le RTC hardware
  *   ✔ Marquer ntp_synced = 1 pour signaler la synchronisation réussie
  *   ✔ Fermer proprement le PCB UDP
  */
void ntp_recv_callback(void *arg,
                       struct udp_pcb *pcb,
                       struct pbuf *p,
                       const ip_addr_t *addr,
                       u16_t port)
{
    /* ----------------------------------------------------------------------
     * 1) Vérification du paquet
     * ---------------------------------------------------------------------- */
    if (p != NULL && p->tot_len >= 48)   // Un paquet NTP valide fait ≥ 48 octets
    {
        /* Pointeur sur la charge utile du paquet UDP */
        uint8_t *payload = (uint8_t *)p->payload;

        /* ------------------------------------------------------------------
         * 2) Extraction du timestamp NTP (32 bits)
         *     Format : big endian (octets 40–43)
         * ------------------------------------------------------------------ */
        uint32_t ntp_seconds =
            (payload[40] << 24) |
            (payload[41] << 16) |
            (payload[42] << 8)  |
             payload[43];

        /* ------------------------------------------------------------------
         * 3) Conversion NTP -> UNIX
         * ------------------------------------------------------------------ */
        uint32_t unix_time = ntp_seconds - NTP_TIMESTAMP_DELTA;

        /* ------------------------------------------------------------------
         * 4) Ajout du fuseau horaire (Belgique = UTC+1)
         * ------------------------------------------------------------------ */
        unix_time += (TIMEZONE_OFFSET * 3600);

        /* ------------------------------------------------------------------
         * 5) Conversion epoch → h/m/s
         * ------------------------------------------------------------------ */


        time_t raw = unix_time;
        struct tm *t = gmtime(&raw);

        DrvRtc_SetDateTime(
            t->tm_year % 100,    // année (25)
            t->tm_mon + 1,       // mois 1–12
            t->tm_mday,          // jour
            t->tm_hour,
            t->tm_min,
            t->tm_sec
        );

        ntp_synced = 1;

        /* Feedback UART */
        char msg[80];
        sprintf(msg,
                "RTC SYNC NTP : 20%02d-%02d-%02d %02d:%02d:%02d\r\n",
                t->tm_year % 100,
                t->tm_mon + 1,
                t->tm_mday,
                t->tm_hour,
                t->tm_min,
                t->tm_sec);
        App_LogPrintf("%s", msg);



    }




    /* ----------------------------------------------------------------------
     * 8) Nettoyage indispensable
     * ---------------------------------------------------------------------- */
    pbuf_free(p);   // Libération du buffer LwIP
    if (pcb != NULL) {
            udp_remove(pcb);
            ntp_pcb = NULL; // On signale au système que le PCB est libéré
        }
}


void Time_FormatIso8601(char *buf, size_t len)
{
    RTC_DateTime dt;
    DrvRtc_GetDateTime(&dt);

    snprintf(buf, len,
        "20%02d-%02d-%02dT%02d:%02d:%02dZ",
        dt.year, dt.month, dt.day,
        dt.hour, dt.min, dt.sec);
}

/* -------------------------------------------------------------------------- */
/*                   ENVOI D’UNE REQUÊTE NTP (Client UDP)                    */
/* -------------------------------------------------------------------------- */
/**
  * @brief  Envoie un paquet NTP à un serveur de temps pour obtenir l’heure.
  *
  * Fonctionnement :
  *   ✔ Création d’un PCB UDP
  *   ✔ Installation de la callback ntp_recv_callback()
  *   ✔ Préparation du paquet NTP (48 octets, mode client)
  *   ✔ Envoi vers serveur NTP (port 123)
  *   ✔ Le PCB reste ouvert jusqu’à la réception → fermeture dans callback
  */
/* -------------------------------------------------------------------------- */
/* ENVOI D’UNE REQUÊTE NTP (Client UDP)                    */
/* -------------------------------------------------------------------------- */
void Ntp_RequestTimeSync(void)
{
    struct pbuf *p;
    ip_addr_t dest_ip;
    err_t err;

    /* 1. NETTOYAGE PRÉVENTIF : Si un ancien PCB traîne (requête précédente échouée), on le supprime */
    if (ntp_pcb != NULL) {
        udp_remove(ntp_pcb);
        ntp_pcb = NULL;
    }

    App_LogPrintf("NTP: Connexion au serveur de temps...\r\n");

    /* 2. Création du nouveau PCB UDP */
    ntp_pcb = udp_new();
    if (!ntp_pcb) {
    	App_LogPrintf("NTP: Erreur alloc PCB (Memoire pleine)\r\n");
        return;
    }

    /* 3. Configuration de la callback */
    udp_recv(ntp_pcb, ntp_recv_callback, NULL);

    /* 4. Adresse IP  */
    ipaddr_aton("216.239.35.0", &dest_ip);

    /* 5. Préparation du buffer NTP */
    uint8_t *buff = (uint8_t *)mem_malloc(NTP_MSG_LEN);
    if (!buff) {
        udp_remove(ntp_pcb);
        ntp_pcb = NULL;
        return;
    }
    memset(buff, 0, NTP_MSG_LEN);
    buff[0] = 0x1B; // Mode Client

    p = pbuf_alloc(PBUF_TRANSPORT, NTP_MSG_LEN, PBUF_RAM);
    if (!p) {
        mem_free(buff);
        udp_remove(ntp_pcb);
        ntp_pcb = NULL;
        return;
    }
    memcpy(p->payload, buff, NTP_MSG_LEN);
    mem_free(buff);

    /* 6. Envoi */
    err = udp_sendto(ntp_pcb, p, &dest_ip, NTP_PORT);
    pbuf_free(p);

    if (err == ERR_OK) {
    	App_LogPrintf("NTP: Requete envoyee...\r\n");
    } else {
    	App_LogPrintf("NTP: Erreur envoi.\r\n");
        // En cas d'erreur immédiate, on libère tout de suite
        udp_remove(ntp_pcb);
        ntp_pcb = NULL;
    }
}

void presence_recv_cb(void *arg, struct udp_pcb *pcb, struct pbuf *p,
                      const ip_addr_t *addr, u16_t port)
{
    if (!p) return;

    // 1. Lire le message pour vérifier que c'est bien "presence"
    char buf[300];
    uint16_t len = (p->tot_len < sizeof(buf) - 1) ? p->tot_len : sizeof(buf) - 1;
    pbuf_copy_partial(p, buf, len, 0);
    buf[len] = '\0';

    // On vérifie si c'est bien un paquet de présence
    if (strstr(buf, "\"presence\"") != NULL)
    {
        // Protection mémoire
        osMutexWait(nodeMutexHandle, osWaitForever);

        int found = 0;
        int empty_idx = -1;

        // A. Est-ce qu'on connait déjà ce voisin ?
        for (int i = 0; i < MAX_NEIGHBORS; i++)
        {
            if (dynamic_node_list[i].active)
            {
                // Compare l'IP reçue avec celle en mémoire
                if (ip_addr_cmp(&dynamic_node_list[i].ip, addr))
                {
                    dynamic_node_list[i].last_seen = HAL_GetTick(); // Mise à jour
                    found = 1;
                    break;
                }
            }
            else if (empty_idx == -1)
            {
                empty_idx = i; // On repère une case vide au cas où
            }
        }

        // B. Nouveau voisin ! On l'ajoute.
        if (!found && empty_idx != -1)
        {
            ip_addr_copy(dynamic_node_list[empty_idx].ip, *addr);
            dynamic_node_list[empty_idx].last_seen = HAL_GetTick();
            dynamic_node_list[empty_idx].active = 1;

            App_LogPrintf("NOUVEAU VOISIN AJOUTE : %s\r\n", ipaddr_ntoa(addr));
        }

        osMutexRelease(nodeMutexHandle);
    }

    pbuf_free(p);
}

/* USER CODE END 4 */

/* USER CODE BEGIN Header_StartDefaultTask */
/**
  * @brief  Function implementing the defaultTask thread.
  * @param  argument: Not used
  * @retval None
  */
/* USER CODE END Header_StartDefaultTask */
void StartDefaultTask(void const * argument)
{
  /* init code for LWIP */
  MX_LWIP_Init();

  extern struct netif gnetif;
  char msg[128];

  // 1. DHCP
  App_LogPrintf("Attente IP DHCP...\r\n");
  while (!netif_is_up(&gnetif) || ip4_addr_isany_val(*netif_ip4_addr(&gnetif))) { osDelay(500); }
  sprintf(msg, "IP Obtenue : %s\r\n", ipaddr_ntoa(&gnetif.ip_addr));
  App_LogPrintf("%s", msg);

  // 2. NTP (Synchronisation Heure)
  int retry_count = 0;
  while (ntp_synced == 0 && retry_count < NTP_MAX_RETRIES)
  {
	  Ntp_RequestTimeSync();
      for (int i = 0; i < 20; i++) { osDelay(100); if (ntp_synced) break; }
      if (!ntp_synced) {
          retry_count++;
          App_LogPrintf(" NTP: essai %d/%d...\r\n", retry_count, NTP_MAX_RETRIES);
      }
  }
  if (ntp_synced) App_LogPrintf(" Heure synchronisée NTP.\r\n");
  else App_LogPrintf(" Démarrage sans NTP (Heure RTC).\r\n");


  // 3. SYSTEME PRET
  App_LogPrintf("\r\n>>> SYSTEME PRET (Appuyez sur BLEU) <<<\r\n");
  system_is_running = 0;


  for(;;) {
      if (HAL_GPIO_ReadPin(USER_Btn_GPIO_Port, USER_Btn_Pin) == GPIO_PIN_SET) {
        osDelay(50);
        while (HAL_GPIO_ReadPin(USER_Btn_GPIO_Port, USER_Btn_Pin) == GPIO_PIN_SET);

        if (!system_is_running) {
        	system_is_running = 1;
        	App_LogPrintf("\r\n>>> SYSTEM STARTED <<<\r\n");

          // Activation UDP
          if (presence_rx_pcb == NULL) {
              presence_rx_pcb = udp_new_ip_type(IPADDR_TYPE_V4);
              if (presence_rx_pcb) {
                  ip_set_option(presence_rx_pcb, SOF_BROADCAST);
                  if (udp_bind(presence_rx_pcb, IP_ADDR_ANY, PRESENCE_PORT) == ERR_OK) {
                      udp_recv(presence_rx_pcb, presence_recv_cb, NULL);
                      App_LogPrintf("UDP presence RX ACTIVE\r\n");
                  }
              }
          }
          // LECTURE INITIALE (AU DEMARRAGE) - SCAN COMPLET DES 10 ENTREES
          App_LogPrintf("--- ETAT DE LA MEMOIRE FRAM AU DEMARRAGE---\r\n");

          NeighborEvent evt_read;
          int found_nb = 0;

          for (int slot = 0; slot < MAX_TRACKED_NEIGHBORS; slot++)
          {
              uint8_t ip_found = 0;
              NeighborEvent last_valid = {0};

              for (int evt_idx = 0; evt_idx < HISTORY_DEPTH; evt_idx++)
              {
                  uint32_t addr =
                      FRAM_NEIGHBOR_BASE_ADDR +
                      (slot * FRAM_NEIGHBOR_BLOCK_SIZE) +
                      (evt_idx * sizeof(NeighborEvent));

                  FRAM_Read(addr, (uint8_t*)&evt_read, sizeof(evt_read));

                  // entrée "valide"
                  if (evt_read.source_ip != 0 && evt_read.source_ip != 0xFF &&
                      evt_read.day >= 1 && evt_read.day <= 31)
                  {
                      ip_found = evt_read.source_ip;
                      last_valid = evt_read; // on garde la dernière entrée valide trouvée
                  }
              }
              int last_valid_idx = -1;
              if (ip_found)
              {
            	  neighbor_ip_map[slot] = ip_found;
            	  neighbor_fram_idx[slot] = (last_valid_idx + 1) % HISTORY_DEPTH;
                  found_nb++;

                  App_LogPrintf("SLOT %d (IP .%d) | 20%02d-%02d-%02d %02d:%02d:%02d | Force: %.2f V\r\n",
                           slot, last_valid.source_ip,
                           last_valid.year, last_valid.month, last_valid.day,
                           last_valid.hour, last_valid.min, last_valid.sec,
                           last_valid.intensity);
              }
              else
              {
                  neighbor_ip_map[slot] = 0;
              }
          }

          if (found_nb == 0) App_LogPrintf("   (Memoire vide)\r\n");
          App_LogPrintf("-----------------------------------\r\n");

          // Reprise des tâches
          osThreadResume(heartBeatTaskHandle);
          osThreadResume(presenceTaskHandle);
          osThreadResume(seismicTaskHandle);
          osThreadResume(clientTaskHandle);

        } else {
            // -----------------------------------------------------------
            //  MODE PAUSE (STOP)
            // -----------------------------------------------------------
        	system_is_running = 0;
        	App_LogPrintf("\r\n>>> SYSTEM STOPPED (PAUSE) <<<\r\n");

            // 1. LOCAL
        	App_LogPrintf("\r\n --- 10 VALEURS LOCALES (FRAM) ---\r\n");
        	App_LogPrintf("Idx | Date       Heure    | Intensite\r\n");
            for(int i=0; i<HISTORY_DEPTH; i++) {
                LocalHistoryItem *item = &local_history[i];
                if (item->max_rms > 0.001f) {
                    sprintf(msg, " %02d | 20%02d-%02d-%02d %02d:%02d:%02d | %.2f V\r\n",
                            i, item->y, item->mo, item->d, item->h, item->m, item->s, item->max_rms);
                    App_LogPrintf("%s", msg);
                }
            }

            // 2. VOISINS
            App_LogPrintf("\r\n --- HISTORIQUE FRAM VOISINS ---\r\n");
            NeighborEvent evt_read;

            for (int slot = 0; slot < MAX_TRACKED_NEIGHBORS; slot++)
            {
                // Vérif si le slot est utilisé
            	App_LogPrintf("\r\n --- VOISIN SLOT %d (IP .%d) ---\r\n", slot, neighbor_ip_map[slot]);

                for (int evt_idx = 0; evt_idx < HISTORY_DEPTH; evt_idx++)
                {
                    uint32_t read_addr = FRAM_NEIGHBOR_BASE_ADDR + (slot * FRAM_NEIGHBOR_BLOCK_SIZE) + (evt_idx * sizeof(NeighborEvent));
                    FRAM_Read(read_addr, (uint8_t*)&evt_read, sizeof(evt_read));

                    if (evt_read.day > 0 && evt_read.day <= 31)
                    {
                        sprintf(msg, "   [%d] 20%02d-%02d-%02d %02d:%02d:%02d | Force: %.2f V\r\n",
                                evt_idx, evt_read.year, evt_read.month, evt_read.day,
                                evt_read.hour, evt_read.min, evt_read.sec, evt_read.intensity);
                        App_LogPrintf("%s", msg);
                    }
                }
            }
            App_LogPrintf("----------------------------------------------------\r\n");

            osThreadSuspend(heartBeatTaskHandle);
            osThreadSuspend(presenceTaskHandle);
            osThreadSuspend(seismicTaskHandle);
            osThreadSuspend(clientTaskHandle);
        }
      }
      osDelay(100);
  }
  /* USER CODE END 5 */
}

/* USER CODE BEGIN Header_LogMessageTask */
/**
* @brief Function implementing the logMessageTask thread.
* @param argument: Not used
* @retval None
*/
/* USER CODE END Header_LogMessageTask */
void LogMessageTask(void const * argument)
{
  /* USER CODE BEGIN LogMessageTask */
  /* Infinite loop */
    for (;;)
    {
        osEvent evt = osMessageGet(messageQueueHandle, osWaitForever);
        if (evt.status == osEventMessage)
        {
            UartMsg *m = (UartMsg *)evt.value.p;

            HAL_UART_Transmit(&huart3,
                              (uint8_t*)m->text,
                              strlen(m->text),
                              HAL_MAX_DELAY);
        }
    }
  /* USER CODE END LogMessageTask */
}

/* USER CODE BEGIN Header_StartClientTask */
/**
* @brief Function implementing the clientTask thread.
* @param argument: Not used
* @retval None
*/
/* USER CODE END Header_StartClientTask */
void StartClientTask(void const * argument)
{
  /* USER CODE BEGIN StartClientTask */
    /* attendre init réseau */
	extern struct netif gnetif;
	    while (!netif_is_up(&gnetif)) osDelay(100);

	    App_LogPrintf("CLIENT DYNAMIQUE DEMARRE (Attente decouverte...)\r\n");

	    for (;;)
	    {

	        // 1. On copie la liste localement pour ne pas bloquer le Mutex trop longtemps
	        ip_addr_t targets[MAX_NEIGHBORS];
	        int target_count = 0;

	        osMutexWait(nodeMutexHandle, osWaitForever);

	        for (int i = 0; i < MAX_NEIGHBORS; i++)
	        {
	            if (dynamic_node_list[i].active)
	            {
	                // Optionnel : Supprimer les vieux noeuds (> 60 secondes sans news)
	                if (HAL_GetTick() - dynamic_node_list[i].last_seen > 60000) {
	                    dynamic_node_list[i].active = 0;
	                    App_LogPrintf("Noeud %s supprime (inactif)\r\n", ipaddr_ntoa(&dynamic_node_list[i].ip));
	                }
	                else {
	                    // On copie l'IP pour la traiter
	                    ip_addr_copy(targets[target_count], dynamic_node_list[i].ip);
	                    target_count++;
	                }
	            }
	        }

	        osMutexRelease(nodeMutexHandle);

	        // 2. On interroge les cibles trouvées
	        for (int i = 0; i < target_count; i++)
	        {
	            // Conversion IP LwIP vers String pour ta fonction existante
	            char ip_str[16];
	            strcpy(ip_str, ipaddr_ntoa(&targets[i]));

	            // On ne s'appelle pas soi-même
	            if (!ip_addr_cmp(&targets[i], &gnetif.ip_addr)) {
	                send_data_request_tcp(ip_str);
	                osDelay(200);
	            }
	        }

	        osDelay(5000); // On recommence le tour toutes les 5 secondes
	    }
  /* USER CODE END StartClientTask */
}

/* USER CODE BEGIN Header_StartServerTask */
/**
* @brief Function implementing the serverTask thread.
* @param argument: Not used
* @retval None
*/
/* USER CODE END Header_StartServerTask */
void StartServerTask(void const * argument)
{
  /* USER CODE BEGIN StartServerTask */
  /* Infinite loop */
    extern struct netif gnetif;
    while (!netif_is_up(&gnetif))
        osDelay(100);
    App_LogPrintf("SERVER TASK STARTED\r\n");

    tcp_server_init(); // <-- nouveau serveur TCP (mise en écoute)
    for(;;)
    {
        osDelay(1); // Le thread reste vivant mais ne fait rien (LwIP gère par interruptions)
    }
  /* USER CODE END StartServerTask */
}

/* USER CODE BEGIN Header_StartHeartBeatTask */
/**
* @brief Function implementing the heartBeatTask thread.
* @param argument: Not used
* @retval None
*/
/* USER CODE END Header_StartHeartBeatTask */
void StartHeartBeatTask(void const * argument)
{
  /* USER CODE BEGIN StartHeartBeatTask */
  /* Infinite loop */
  for(;;)
  {
    HAL_GPIO_TogglePin(LD1_GPIO_Port, LD1_Pin);
    osDelay(500); // 1 Hz (500ms ON, 500ms OFF)
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
  /* User can add his own implementation to report the HAL error return state */
  __disable_irq();
  while (1)
  {
  }
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
  /* User can add his own implementation to report the file name and line number,
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */
