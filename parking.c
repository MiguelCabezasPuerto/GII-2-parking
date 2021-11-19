#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/ipc.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/sem.h>
#include <sys/msg.h>
#include <signal.h>
#include <sys/shm.h>

#include "parking.h"

//Lib
#define TAM_ACERA 80
#define NUM_ACERAS 3
#define CARRETERA 2
#define LINEA 1
#define PARKING 0
#define LIBRE '0'
#define OCUPADA '1'
#define RESERVADA '2'
#define APARCAR 1
#define DESAPARCAR 2
//OFFST
#define TIPO_MSG_COMMIT 200
#define OFFT_CARRETERA (TAM_ACERA * CARRETERA)
#define OFFT_LINEA (TAM_ACERA * LINEA)
#define OFFT_PARKING (TAM_ACERA * PARKING)
#define OFFST_PIDS 960
#define OFFT_MEJORAJUSTE 240
#define OFFT_PEORAJUSTE 480
#define OFFT_SIGAJUSTE 720
#define OFFT_PRIMRAJUSTE 0
//Values
#define MAX_V_CARRETERA 240
#define MIN_V_CARRETERA 160
//Factores
#define FACT_PRIMER 0
#define FACT_MEJOR 10000
#define FACT_PEOR 40000
#define FACT_SIG 60000
//Sem para que solo entre un proceso a la vez en los diferentes algoritmos
#define SEM_SYNC 6
#define SEM_ALG_PRA 325
#define SEM_ALG_SIG 326
#define SEM_ALG_MEJOR 328
#define SEM_ALG_PEOR 329
//Sem para que no se adelanten los coches
#define SEM_ALG_PA 330
#define SEM_ALG_SA 331
#define SEM_ALG_MA 332
#define SEM_ALG_PEA 333
//Sem offst
#define SEM_MEJORAJUSTE 80
#define SEM_PEORAJUSTE 160
#define SEM_SIGUAJUSTE 240
#define SEM_PRIMRAJUSTE 0

typedef struct PARKING_mensajeBiblioteca mensaje;

typedef pid_t __pid_t;

//fprintf en stderr
void error(char *errorInfo);

//Manejadoras
void ctrlC(int numSennal);
void alarma(int numSennal);

//Parametros
int validar_parametros(int argc, char *argv[]);

//Crear ipc
int crea_memoria_compartida(size_t tam);
int crea_buzon();
int crea_semaforo(int);
char *crea_punteroChar(int memoria);

//Borrar ipc
void clear();
void borra_buzon(int);
void borra_semaforo(int);
void borra_memoria(int);
void borra_puntero(char*);

//Gestion semaforos
void doWait(int semid, int numSem);
void doSignal(int semid, int numSem);
void doWaitMultiple(int semid,int numSem,int cantidad);  //operaciOn atOmica aunque sea decremento de varias unidades!
void doSignalMultiple(int semid,int numSem,int cantidad);//operaciOn atOmica aunque sea incremento de varias unidades!
void inicia_semaforo(int semid, int numSem, int valor);

//Algoritmos
int f_llegada_PrimerAjuste(HCoche);
int f_llegadaB_SigAjuste(HCoche);
int f_llegadaC_MejorAjuste(HCoche);
int f_llegadaD_PeorAjuste(HCoche);

//Globales
int ID_memoria, ID_buzon, ID_semaforo, TAMlib, numHijos;
char *ID_memptr;

void clear()
{
    int i;
    __pid_t *ID_memptrPid = (__pid_t *)ID_memptr;

    if (ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t)] != getpid())
        return;

    for (i = 0; i < numHijos + 1; i++)
    {
        kill(ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t) + i + 1], SIGINT);
    }

    borra_semaforo(ID_semaforo);
    borra_buzon(ID_buzon);
    borra_puntero(ID_memptr);
    borra_memoria(ID_memoria);
}

int f_llegada_PrimerAjuste(HCoche hc)
{
    int i, j, pos, valido = 1;
    int longCoche = PARKING_getLongitud(hc);

    if (longCoche > TAM_ACERA)
    {
        return -1;
    }

    doWait(ID_semaforo, SEM_ALG_PRA);

    for (i = 0; i < TAM_ACERA; i++)
    {
        if (ID_memptr[i + TAMlib] == LIBRE)
        {
            if (i + longCoche - 1 >= TAM_ACERA)
            {
                doSignal(ID_semaforo, SEM_ALG_PRA);
                return -1;
            }
            pos = i;
            for (j = i; j < pos + longCoche; j++)
            {
                if (ID_memptr[j + TAMlib] != LIBRE)
                {
                    valido = 0;
                    break;
                }
            }
            if (valido != 0)
            {
                for (j = pos; j < pos + longCoche; j++)
                {
                    ID_memptr[j + TAMlib] = RESERVADA;
                }
                doSignal(ID_semaforo, SEM_ALG_PRA);
                return pos;
            }
            valido = 1;
        }
    }
    doSignal(ID_semaforo, SEM_ALG_PRA);
    return -1;
}

int f_llegadaB_SigAjuste(HCoche hc)
{
    int i, j, l, pos, pos2, k, contarCerosAntes, contarCerosDespues, contarCerosGuille;
    static int ultimoOcupado = 0;
    int longitud = PARKING_getLongitud(hc);

    //Caso raro, en caso que el ultimo coche que aparcO ya se haya ido entonces miramos si el hueco que dejO ahI
    //puede entrar el nuevo coche(por hueco que dejO me refiero al hueco que ocupaba mAs algUn hueco desaprovechado que pudiese haber

    doWait(ID_semaforo, SEM_ALG_SIG);
    if (ID_memptr[TAMlib + ultimoOcupado + OFFT_SIGAJUSTE] == LIBRE)
    {
        contarCerosGuille = 0;
        l = ultimoOcupado;
        // l > 0 para que no valga -1 y ultimo ocupado funcione desde 0
        while (l > 0 && ID_memptr[TAMlib + l + OFFT_SIGAJUSTE] == LIBRE)
        {
            contarCerosGuille++;
            l--;
        }

        //Cuento desde el ultimo ocupadao - la long del anterior que se fue..
        ultimoOcupado = ultimoOcupado - contarCerosGuille;
    }
    //CASO GENERAL, se empieza a buscar a partir de la posicion del ultimo ocupado
    for (i = ultimoOcupado; i < TAM_ACERA; i++)
    {
        pos = j = i;
        contarCerosDespues = 0;
        while (j < TAM_ACERA && ID_memptr[TAMlib + j + OFFT_SIGAJUSTE] == LIBRE)
        {
            contarCerosDespues++;
            j++;
        }
        if (contarCerosDespues >= longitud)
        {
            for (k = pos; k < pos + longitud; k++)
            {
                ID_memptr[TAMlib + k + OFFT_SIGAJUSTE] = RESERVADA;
            }
            ultimoOcupado = pos + longitud - 1;
            doSignal(ID_semaforo, SEM_ALG_SIG);
            return pos;
        }
    }
    //Empieza de nuevo
    for (i = 0; i < ultimoOcupado; i++)
    {
        pos2 = j = i;
        contarCerosAntes = 0;
        while (j < TAM_ACERA && ID_memptr[TAMlib + j + OFFT_SIGAJUSTE] == LIBRE)
        {
            contarCerosAntes++;
            j++;
        }
        if (contarCerosAntes >= longitud)
        {
            for (k = pos2; k < pos2 + longitud; k++)
            {
                ID_memptr[TAMlib + k + OFFT_SIGAJUSTE] = RESERVADA;
            }
            ultimoOcupado = pos2 + longitud - 1;
            doSignal(ID_semaforo, SEM_ALG_SIG);
            return pos2;
        }
    }
    doSignal(ID_semaforo, SEM_ALG_SIG);
    return -1;
}

int f_llegadaC_MejorAjuste(HCoche hc)
{

    int longitud = PARKING_getLongitud(hc);
    int factor = TAMlib;
    int menor, posInicial, posFinal, contarCeros, i, j, pos;
    menor = TAM_ACERA + 1;
    posInicial = -1;
    posFinal = -1;

    doWait(ID_semaforo, SEM_ALG_MEJOR);

    for (i = 0; i < TAM_ACERA;)
    {
        contarCeros = 0;
        if (ID_memptr[i + factor + OFFT_MEJORAJUSTE] == LIBRE)
        {
            pos = j = i;
            while (j < TAM_ACERA && ID_memptr[j + factor + OFFT_MEJORAJUSTE] == LIBRE)
            {
                contarCeros++;
                j++;
            }
            if (contarCeros >= longitud)
            {
                if (contarCeros < menor)
                {
                    menor = contarCeros;
                    posInicial = pos;
                    posFinal = j - 1;
                }
            }
            i = j;
        }
        else
            i++;
    }
    if (posInicial != -1)
    {
        for (i = posInicial; i < longitud + posInicial; i++)
        {
            ID_memptr[i + factor + OFFT_MEJORAJUSTE] = RESERVADA;
        }
    }
    doSignal(ID_semaforo, SEM_ALG_MEJOR);
    return posInicial;
}

int f_llegadaD_PeorAjuste(HCoche hc)
{
    int mayor, posInicial, posFinal, i, j, contarCeros, pos;
    int longitud = PARKING_getLongitud(hc);

    mayor = -1;
    posInicial = -1;
    posFinal = -1;

    doWait(ID_semaforo, SEM_ALG_PEOR);
    for (i = 0; i < TAM_ACERA;)
    {
        contarCeros = 0;
        if (ID_memptr[TAMlib + i + OFFT_PEORAJUSTE] == LIBRE)
        {
            pos = j = i;
            while (j < TAM_ACERA && ID_memptr[TAMlib + j + OFFT_PEORAJUSTE] == LIBRE)
            {
                contarCeros++;
                j++;
            }
            if (contarCeros >= longitud)
            {
                if (contarCeros > mayor)
                {
                    mayor = contarCeros;
                    posInicial = i;
                    posFinal = j - 1;
                }
            }
            i = j;
        }
        else
            i++;
    }
    if (posInicial != -1)
    {
        for (i = posInicial; i < posInicial + longitud; i++)
        {
            ID_memptr[TAMlib + i + OFFT_PEORAJUSTE] = RESERVADA;
        }
    }
    doSignal(ID_semaforo, SEM_ALG_PEOR);
    return posInicial;
}

void iniciar_Aceras()
{
    int i;
    //PARA ZONA APARCAR + LINEA DISCONTINUA + CARRETERA * 4 Algoritmos
    for (i = TAMlib; i < (TAM_ACERA * NUM_ACERAS) * 4 + TAMlib; i++)
    {
        ID_memptr[i] = LIBRE;
    }
}

void aparcar_commit(HCoche hc)
{
    mensaje temp;
    temp.hCoche = 0;
    temp.subtipo = 0;
    if ((PARKING_getAlgoritmo(hc)) == PRIMER_AJUSTE)
    {
        doSignalMultiple(ID_semaforo,SEM_ALG_PA,PARKING_getNUmero(hc)+1);  //es atOmica ! Hace tantos signal de su semaforo como su numero de coche mAs uno
    }
    else if ((PARKING_getAlgoritmo(hc)) == MEJOR_AJUSTE)  
    {
        doSignalMultiple(ID_semaforo,SEM_ALG_MA,PARKING_getNUmero(hc)+1);
    }
    else if ((PARKING_getAlgoritmo(hc)) == SIGUIENTE_AJUSTE)
    {
        doSignalMultiple(ID_semaforo,SEM_ALG_SA,PARKING_getNUmero(hc)+1);
    }
    else if ((PARKING_getAlgoritmo(hc)) == PEOR_AJUSTE)
    {
        doSignalMultiple(ID_semaforo,SEM_ALG_PEA,PARKING_getNUmero(hc)+1);
    }
}

void permiso_avance(HCoche hc)
{
    int off, sem;
    int i, valido = 1;
    int longCoche = PARKING_getLongitud(hc);
    int posIrX = PARKING_getX2(hc);
    int posIrY = PARKING_getY2(hc);
    int posEstaX = PARKING_getX(hc);
    int posEstaY = PARKING_getY(hc);

    if ((PARKING_getAlgoritmo(hc)) == MEJOR_AJUSTE)
    {
        sem = SEM_MEJORAJUSTE;
        off = OFFT_MEJORAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == PEOR_AJUSTE)
    {
        sem = SEM_PEORAJUSTE;
        off = OFFT_PEORAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == SIGUIENTE_AJUSTE)
    {
        sem = SEM_SIGUAJUSTE;
        off = OFFT_SIGAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == PRIMER_AJUSTE)
    {
        sem = SEM_PRIMRAJUSTE;
        off = OFFT_PRIMRAJUSTE;
    }
    //linea-parking o parking-linea o carretera-linea
    if (posIrY == LINEA && posEstaY == PARKING) //de parking a linea
    {
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posIrX + i + OFFT_LINEA + off] = OCUPADA;
        }
    }
    else if (posIrY == PARKING && posEstaY == LINEA) //linea-parking
    {
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posIrX + i + OFFT_PARKING + off] = OCUPADA;
        }
    }
    else if (posIrY == LINEA && posEstaY == CARRETERA) //road-linea
    {
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posIrX + i + OFFT_LINEA + off] = OCUPADA;
        }
    }
    else if (posIrY == CARRETERA && posEstaY == CARRETERA) //de road a road
    {
        if (posEstaX + TAM_ACERA * CARRETERA > MAX_V_CARRETERA)
        {
            return;
        }
        else if (posIrX + TAM_ACERA * CARRETERA < MIN_V_CARRETERA)
        {
            return;
        }
        doWait(ID_semaforo, posIrX + SEM_SYNC + sem);
        ID_memptr[TAMlib + posIrX + OFFT_CARRETERA + off] = OCUPADA;
    }
    else if (posIrY == CARRETERA && posEstaY == LINEA) //de linea a road
    {
        //!! OJO !! del culo -> morro
        for (i = longCoche - 1; i >= 0; i--)
        {
            doWait(ID_semaforo, posIrX + i + SEM_SYNC + sem);
            ID_memptr[TAMlib + posIrX + i + OFFT_CARRETERA + off] = OCUPADA;
        }
    }
}

void permiso_avance_commit(HCoche hc)
{
    int longCoche = PARKING_getLongitud(hc);
    int posVeniaX = PARKING_getX2(hc);
    int posVeniaY = PARKING_getY2(hc);
    int posEstaX = PARKING_getX(hc);
    int posEstaY = PARKING_getY(hc);
    int off, sem, i;

    if ((PARKING_getAlgoritmo(hc)) == MEJOR_AJUSTE)
    {
        sem = SEM_MEJORAJUSTE;
        off = OFFT_MEJORAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == PEOR_AJUSTE)
    {
        sem = SEM_PEORAJUSTE;
        off = OFFT_PEORAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == SIGUIENTE_AJUSTE)
    {
        sem = SEM_SIGUAJUSTE;
        off = OFFT_SIGAJUSTE;
    }
    else if ((PARKING_getAlgoritmo(hc)) == PRIMER_AJUSTE)
    {
        sem = SEM_PRIMRAJUSTE;
        off = OFFT_PRIMRAJUSTE;
    }
    if (posVeniaY == LINEA && posEstaY == CARRETERA) //de linea a road
    {
        // Libero linea
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posVeniaX + i + OFFT_LINEA + off] = LIBRE;
        }
        // Libero parking
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posVeniaX + i + OFFT_PARKING + off] = LIBRE;
        }
    }
    else if (posVeniaY == CARRETERA && posEstaY == LINEA) //de road a linea
    {
        //Libero carretera
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posVeniaX + i + OFFT_CARRETERA + off] = LIBRE;
            doSignal(ID_semaforo, posVeniaX + i + SEM_SYNC + sem);
        }
    }
    else if (posVeniaY == LINEA && posEstaY == PARKING) //de linea a parking
    {
        //libero linea
        for (i = 0; i < longCoche; i++)
        {
            ID_memptr[TAMlib + posVeniaX + i + OFFT_LINEA + off] = LIBRE;
        }
    }
    else if (posVeniaY == CARRETERA && posEstaY == CARRETERA) //de road a road
    {
        // Si el morro esta desapareciendo (se va de road a linea)
        // la pos anterior esta en road, la liberamos...
        if (posVeniaX + longCoche + OFFT_CARRETERA > MAX_V_CARRETERA)
        {
        }
        else
        {
            ID_memptr[TAMlib + posVeniaX + longCoche - 1 + OFFT_CARRETERA + off] = LIBRE;
            doSignal(ID_semaforo, posVeniaX + longCoche - 1 + SEM_SYNC + sem);
        }
    }
}

int main(int argc, char *argv[])
{
    int i;
    int numSem, tamMem;
    __pid_t pid;
    mensaje msgLib;
    mensaje msgBufferPA, msgBufferMA, msgBufferPEOR, msgBufferSig;

    if ((!validar_parametros(argc, argv)))
    {
        printf(" Debe introducir entre dos y tres argumentos de la siguiente forma:\n");
        printf("\tENTERO >= 0 (representa la rapidez con la que ocurren los acontecimientos => 0\n");
        printf("\trapidez maxima, cuanto mayor el numero menor rapidez\n");
        printf("\tNUM_CHOFERES > 0\n");
        printf("\tD (para activar el modo con depuracion\n\n");
        return 1;
    }
    //Cuando llamemos a exit(n) llamra a nuestra funcion clear
    atexit(clear);

    TIPO_FUNCION_LLEGADA f_llegadas[] = {f_llegada_PrimerAjuste, f_llegadaB_SigAjuste, f_llegadaC_MejorAjuste, f_llegadaD_PeorAjuste};

    //IPC
    numHijos = atoi(argv[2]);
    TAMlib = PARKING_getTamaNoMemoriaCompartida();

    tamMem = TAMlib + (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char) + (atoi(argv[2]) + 1) * sizeof(__pid_t));
    numSem = PARKING_getNSemAforos() + 4 + 4 + (4 * TAM_ACERA); // +4 Por 4 algoritmos // 5 + 4 + 4 * 80 = 329 // +4 para no adelantarse (1 por algoritmo)

    ID_semaforo = crea_semaforo(numSem);

    for (i = SEM_SYNC; i < numSem; i++)
        inicia_semaforo(ID_semaforo, i, 1);

    ID_buzon = crea_buzon();
    ID_memoria = crea_memoria_compartida(tamMem);
    ID_memptr = crea_punteroChar(ID_memoria);

    //Guardamos el pid del padre
    __pid_t *ID_memptrPid = (__pid_t *)ID_memptr;
    ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t)] = getpid();

    iniciar_Aceras();

    if (PARKING_inicio(atoi(argv[1]), f_llegadas, ID_semaforo, ID_buzon, ID_memoria, (int)argv[3]) == -1)
    {
        error("Error PARKING_inicio");
        exit(1);
    }

    // Primeros mensajes
    msgBufferPA.tipo = TIPO_MSG_COMMIT + 1;
    msgBufferMA.tipo = TIPO_MSG_COMMIT + 1 + FACT_MEJOR;
    msgBufferPEOR.tipo = TIPO_MSG_COMMIT + 1 + FACT_PEOR;
    msgBufferSig.tipo = TIPO_MSG_COMMIT + 1 + FACT_SIG;

    msgsnd(ID_buzon, &msgBufferPA, sizeof(mensaje) - sizeof(long), 0);
    msgsnd(ID_buzon, &msgBufferMA, sizeof(mensaje) - sizeof(long), 0);
    msgsnd(ID_buzon, &msgBufferPEOR, sizeof(mensaje) - sizeof(long), 0);
    msgsnd(ID_buzon, &msgBufferSig, sizeof(mensaje) - sizeof(long), 0);

    switch (fork())
    {
    case -1:
        error("Error al crear hijo fork()");
        exit(6);
    case 0: //HIJO ALARMERO
        ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t) + 1] = getpid();
        signal(SIGALRM, alarma);
        alarm(30);
        pause();
        return 0;
    default: //Padre
        for (i = 0; i < atoi(argv[2]); i++)
        {
            ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t) + i + 2] = pid = fork();

            if (pid == 0) // Hijo, terminamos for
            {
                break;
            }
            if (pid == -1)
            {
                error("Error al crear hijo fork()");
                exit(6);
            }
        }
        if (pid == 0) // LOgica del hijo
        {
            mensaje msgBuffer;
            while (666)
            {
                msgrcv(ID_buzon, &msgLib, sizeof(mensaje) - sizeof(long), 100, 0);
                if (msgLib.subtipo == APARCAR)
                {
                    if ((PARKING_getAlgoritmo(msgLib.hCoche)) == PRIMER_AJUSTE)
                    {
                       doWaitMultiple(ID_semaforo,SEM_ALG_PA,PARKING_getNUmero(msgLib.hCoche)); //atOmica ! por lo que si no puede hacer tantos wait en bloque como su numero de coche no hace ninguno y se queda esperando!
                    }
                    else if ((PARKING_getAlgoritmo(msgLib.hCoche)) == SIGUIENTE_AJUSTE)
                    {
                        doWaitMultiple(ID_semaforo,SEM_ALG_SA,PARKING_getNUmero(msgLib.hCoche));
                    }
                    else if ((PARKING_getAlgoritmo(msgLib.hCoche)) == MEJOR_AJUSTE)
                    {
                        doWaitMultiple(ID_semaforo,SEM_ALG_MA,PARKING_getNUmero(msgLib.hCoche));
                    }
                    else if ((PARKING_getAlgoritmo(msgLib.hCoche)) == PEOR_AJUSTE)
                    {
                        doWaitMultiple(ID_semaforo,SEM_ALG_PEA,PARKING_getNUmero(msgLib.hCoche));
                    }
                    PARKING_aparcar(msgLib.hCoche, NULL, aparcar_commit, permiso_avance, permiso_avance_commit);
                }
                else if (msgLib.subtipo == DESAPARCAR)
                {
                    PARKING_desaparcar(msgLib.hCoche, NULL, permiso_avance, permiso_avance_commit);
                }
            }
        }
        else //PADRE
        {
            signal(SIGINT, ctrlC);
            PARKING_simulaciOn();
            pause();
        }
    }

    return 0;
}

//Parametros
int validar_parametros(int argc, char *argv[])
{
    if (argc < 3 || argc > 4)
    {
        return 0;
    }

    if (argc == 3)
    {
        if ((atoi(argv[1])) < 0 || (atoi(argv[2])) <= 0)
        {
            return 0;
        }
        return 1;
    }
    if (argc == 4)
    {
        if ((atoi(argv[1])) < 0 || (atoi(argv[2])) <= 0 || (strcmp(argv[3], "D") != 0))
        {
            return 0;
        }
        return 1;
    }

    return 0;
}

//Manejadoras
void ctrlC(int numSennal)
{
    signal(numSennal, SIG_IGN);

    __pid_t *ID_memptrPid = (__pid_t *)ID_memptr;

    if (ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t)] != getpid())
        return;

    PARKING_fin(1);

    exit(0);
}
void alarma(int numSennal)
{
    __pid_t *ID_memptrPid = (__pid_t *)ID_memptr;
    PARKING_fin(1);

    kill(ID_memptrPid[TAMlib / sizeof(__pid_t) + OFFST_PIDS / sizeof(__pid_t)], SIGINT);
}

//Error
void error(char *errorInfo)
{
    fprintf(stderr, "%s\n", errorInfo);
}

//Semaforo
int crea_semaforo(int numsems)
{
    int semaforo;
    semaforo = semget(IPC_PRIVATE, numsems, IPC_CREAT | 0600);
    if (semaforo == -1)
    {
        perror(NULL);
        error("Error al crear semaforo");
        exit(1);
    }
    return semaforo;
}
void borra_semaforo(int numSem)
{
    if (semctl(numSem, 0, IPC_RMID) == -1)
    {
        perror(NULL);
        error("Error al borrar semaforo");
    }
}
void inicia_semaforo(int semid, int numSem, int valor)
{
    union semun {
        int val;
        struct semid_ds *buf;
        unsigned short *array;
    } argument;
    argument.val = valor;

    if (semctl(semid, numSem, SETVAL, argument) < 0)
    {
        perror(NULL);
        error("Error iniciando semaforo");
    }
}
void doSignal(int semid, int numSem)
{
    struct sembuf sops;
    sops.sem_num = numSem;
    sops.sem_op = 1;
    sops.sem_flg = 0;

    if (semop(semid, &sops, 1) == -1)
    {
        perror(NULL);
        error("Error al hacer Signal");
    }
}

void doSignalMultiple(int semid,int numSem,int cantidad){
    struct sembuf sops;
    sops.sem_num = numSem;
    sops.sem_op = cantidad;
    sops.sem_flg = 0;

    if (semop(semid, &sops, 1) == -1)
    {
        perror(NULL);
        error("Error al hacer Wait");
    }
}


void doWaitMultiple(int semid,int numSem,int cantidad){
	 struct sembuf sops;
    sops.sem_num = numSem;
    sops.sem_op = -cantidad;
    sops.sem_flg = 0;

    if (semop(semid, &sops, 1) == -1)
    {
        perror(NULL);
        error("Error al hacer Wait");
    }
}

void doWait(int semid, int numSem)
{
    struct sembuf sops;
    sops.sem_num = numSem;
    sops.sem_op = -1;
    sops.sem_flg = 0;

    if (semop(semid, &sops, 1) == -1)
    {
        perror(NULL);
        error("Error al hacer Wait");
    }
}

//Buzon
int crea_buzon()
{
    int temp;
    temp = msgget(IPC_PRIVATE, IPC_CREAT | 0600);
    if (temp == -1)
    {
        perror(NULL);
        error("Error al crear buzon");
        borra_semaforo(ID_semaforo);
        exit(2);
    }
    return temp;
}
void borra_buzon(int buzon)
{
    if (msgctl(buzon, IPC_RMID, NULL) == -1)
    {
        perror(NULL);
        error("Error al borrar buzon");
    }
}

//Memoria compartida
int crea_memoria_compartida(size_t tam)
{
    int temp = shmget(IPC_PRIVATE, tam, IPC_CREAT | 0600);
    if (temp == -1)
    {
        perror(NULL);
        error("Error al crear memoria compartida");
        borra_semaforo(ID_semaforo);
        borra_buzon(ID_buzon);
        exit(3);
    }
    return temp;
}
void borra_memoria(int memoria)
{
    if (shmctl(memoria, IPC_RMID, NULL) == -1)
    {
        perror(NULL);
        error("Error al borrar la memoria compartida");
    }
}

//Puntero a memoria compartida
char *crea_punteroChar(int memoria)
{
    char *temp;
    temp = (char *)shmat(memoria, NULL, 0);
    if (temp == (void *)-1)
    {
        perror(NULL);
        error("Error al crear puntero a memoria compartida");
        borra_semaforo(ID_semaforo);
        borra_buzon(ID_buzon);
        borra_memoria(ID_memoria);
        exit(4);
    }
    return temp;
}
void borra_puntero(char *memPtr)
{
    if (shmdt((void *)memPtr) == -1)
    {
        perror(NULL);
        error("Error al borrar puntero a memoria compartida");
    }
}
