// parking.cpp: define el punto de entrada de la aplicación de consola.
//

// prueba.cpp: define el punto de entrada de la aplicaci�n de consola.
//

#include "stdafx.h"
#include <stdio.h>
#include <Windows.h>
#include "parking2.h"

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

//Sem offst
#define SEM_MEJORAJUSTE 80
#define SEM_PEORAJUSTE 160
#define SEM_SIGUAJUSTE 240
#define SEM_PRIMRAJUSTE 0

//SEMAFOROS PARA QUE NO SE ADELANTEN
HANDLE * semaforos_sig;
HANDLE * semaforos_peor;
HANDLE * semaforos_mejor;
HANDLE * semaforos_primer;

//SEMAFOROS PARA QUE NO SE CHOQUEN
HANDLE * ID_semaforo;

//SEMAFOROS PARA QUE ENTRE SOLO UNA A LA VEZ A MODIFICAR EN LOS AJUSTES
HANDLE  sem_PRIMAJUSTE;
HANDLE  sem_SIGAJUSTE;
HANDLE  sem_PEORAJUSTE;
HANDLE  sem_MEJORAJUSTE;

//EVENTOS PARA ESPERAR A LA COPIA DE HC EN APARCAR
HANDLE preaparcarPrimAjuste, preaparcarSigAjuste, preaparcarMejAjuste, preaparcarPeorAjuste; 

//EVENTOS PARA ESPERAR A LA COPIA DE HC EN DESAPARCAR
HANDLE  predesaparcarPrimAjuste, predesaparcarSigAjuste, predesaparcarMejAjuste, predesaparcarPeorAjuste; //evento para esperar al hilo desaparcador.


//VECTOR CON LA CARRETERA,ACERA Y LINEAS DE TODOS LOS ALGORITMOS
char *ID_memptr;
int tamMem;


//ENLAZADO
int(*PARKING2_inicio)(TIPO_FUNCION_LLEGADA *, TIPO_FUNCION_SALIDA *, LONG, BOOL);
int(*PARKING2_aparcar)(HCoche, void *datos, TIPO_FUNCION_APARCAR_COMMIT, TIPO_FUNCION_PERMISO_AVANCE, TIPO_FUNCION_PERMISO_AVANCE_COMMIT);
int(*PARKING2_desaparcar)(HCoche, void *datos,
	TIPO_FUNCION_PERMISO_AVANCE,
	TIPO_FUNCION_PERMISO_AVANCE_COMMIT);
int(*PARKING2_getNUmero)(HCoche);
int(*PARKING2_getLongitud)(HCoche);
int(*PARKING2_getPosiciOnEnAcera)(HCoche);
int(*PARKING2_getTServ)(HCoche);
void(*PARKING2_getDatos)(HCoche);

int(*PARKING2_getX)(HCoche);

int(*PARKING2_getY)(HCoche);

int(*PARKING2_getX2)(HCoche);
int(*PARKING2_getY2)(HCoche);
int(*PARKING2_getAlgoritmo)(HCoche);
FARPROC PARKING2_fin;

void error(const char *errorInfo);
int WINAPI validar_parametros(int argc, char *argv[]);
HANDLE WINAPI crea_memoria_compartida(size_t tam);
char * WINAPI crea_punteroChar(HANDLE memoria);
void iniciar_Aceras();
void aparcar_commit(HCoche hc);
void permiso_avance(HCoche hc);
void permiso_avance_commit(HCoche hc);
DWORD WINAPI preAparcarPrim(LPVOID hc);
DWORD WINAPI preDesaparcarPrim(LPVOID hc);
DWORD WINAPI preAparcarSig(LPVOID hc);
DWORD WINAPI preDesaparcarSig(LPVOID hc);
DWORD WINAPI preAparcarM(LPVOID hc);
DWORD WINAPI preDesaparcarM(LPVOID hc);
DWORD WINAPI preAparcarP(LPVOID hc);
DWORD WINAPI preDesaparcarP(LPVOID hc);
int  f_llegada_PrimerAjuste(HCoche hc);
int  f_llegadaB_SigAjuste(HCoche hc);
int  f_llegadaC_MejorAjuste(HCoche hc);
int f_llegadaD_PeorAjuste(HCoche hc);
int  f_salida_PrimerAjuste(HCoche hc);
int f_salidaB_SigAjuste(HCoche hc);
int  f_salidaC_MejorAjuste(HCoche hc);
int  f_salidaD_PeorAjuste(HCoche hc);
void doWait(int numSem);
void doSignal(int numSem);
void doWaitPrim(int numSem);
void doSignalPrim(int numSem);
HANDLE WINAPI crea_semaforo();
HANDLE WINAPI crea_semaforo2();

TIPO_FUNCION_LLEGADA  f_llegadas[] = { f_llegada_PrimerAjuste, f_llegadaB_SigAjuste, f_llegadaC_MejorAjuste, f_llegadaD_PeorAjuste };

TIPO_FUNCION_SALIDA  f_salidas[] = { f_salida_PrimerAjuste, f_salidaB_SigAjuste, f_salidaC_MejorAjuste, f_salidaD_PeorAjuste };


DWORD WINAPI preAparcarPrim(LPVOID hc) {
	HCoche coche = (HCoche)hc;
	int numCoche = PARKING2_getNUmero(coche);
	fprintf(stderr, "Llamo a aparcar %d\n\n", PARKING2_getNUmero(coche));
	PARKING2_aparcar(coche, NULL, aparcar_commit, permiso_avance, permiso_avance_commit);
	int i;
	
	return 0;
}
DWORD WINAPI preDesaparcarPrim(LPVOID hc) {
	HCoche coche = (HCoche)hc;
	int i;
	
	PARKING2_desaparcar(coche, NULL, permiso_avance, permiso_avance_commit);
	
	return 0;
}
DWORD WINAPI preAparcarSig(LPVOID hc) {
	/*HCoche *coche = (HCoche *)hc;
	HCoche car = *(coche);
	PulseEvent(preaparcarSigAjuste);
	PARKING2_aparcar(car, NULL, aparcar_commit, permiso_avance, permiso_avance_commit);

	return 0;*/
	return -2;
}
DWORD WINAPI preDesaparcarSig(LPVOID hc) {
	/*HCoche *coche = (HCoche *)hc;
	HCoche car = *(coche);
	PulseEvent(predesaparcarSigAjuste);
	PARKING2_desaparcar(car, NULL, permiso_avance, permiso_avance_commit);
	return 0;*/
	return -2;
}

DWORD WINAPI preAparcarM(LPVOID hc) {
	/*HCoche coche = (HCoche)hc;

	
	PARKING2_aparcar(coche, NULL, aparcar_commit, permiso_avance, permiso_avance_commit);

	return 0;*/
	return -2;
}
DWORD WINAPI preDesaparcarM(LPVOID hc) {
	/*HCoche coche = (HCoche)hc;
	
	
	PARKING2_desaparcar(coche, NULL, permiso_avance, permiso_avance_commit);
	return 0;*/
	return -2;
}





int  f_salida_PrimerAjuste(HCoche hc) {
	fprintf(stderr, "Llamo a desaparcar %d\n\n", PARKING2_getNUmero(hc));
	CreateThread(NULL, 0, preDesaparcarPrim, (LPVOID)hc, 0, NULL);
	
	return 0;
	//return -2;
}

int  f_salidaB_SigAjuste(HCoche hc) {
	/*predesaparcarSigAjuste= CreateEvent(NULL, 0, 0, "predesaparcarSigAjuste");
	CreateThread(NULL, 0, preDesaparcarSig, &hc, 0, NULL);
	WaitForSingleObject(predesaparcarSigAjuste, INFINITE);
	return 0;*/
	return -2;
}
int  f_salidaC_MejorAjuste(HCoche hc) {
	/*predesaparcarMejAjuste = CreateEvent(NULL, 0, 0, "predesaparcarMejAjuste");
	CreateThread(NULL, 0, preDesaparcarM, &hc, 0, NULL);
	WaitForSingleObject(predesaparcarMejAjuste, INFINITE);
	return 0;*/
	return -2;
}
int  f_salidaD_PeorAjuste(HCoche hc) {
	return -2;
}

int  f_llegada_PrimerAjuste(HCoche hc)
{
	WaitForSingleObject(sem_PRIMAJUSTE, INFINITE);

	int i, j, pos, valido = 1;
	int longCoche = PARKING2_getLongitud(hc);
	char temp;
	int numCoche = PARKING2_getNUmero(hc);
	doWaitPrim(numCoche);
	
	
	if (longCoche > TAM_ACERA)
	{
		return -1;
	}
	for (i = 0; i < TAM_ACERA; i++)
	{
		if (ID_memptr[i] == LIBRE)
		{
			if (i + longCoche - 1 >= TAM_ACERA)
			{
				return -1;
			}
			pos = i;
			for (j = i; j < pos + longCoche; j++)
			{
				if (ID_memptr[j] != LIBRE)
				{
					valido = 0;
					break;
				}
			}
			if (valido != 0)
			{
				for (j = pos; j < pos + longCoche; j++)
				{
					ID_memptr[j] = RESERVADA;
				}
				
				CreateThread(NULL, 0, preAparcarPrim, (LPVOID)hc, 0, NULL);
				ReleaseSemaphore(sem_PRIMAJUSTE, 1, NULL);
				return pos;
			}
			valido = 1;
		}
	}
	ReleaseSemaphore(sem_PRIMAJUSTE, 1, NULL);
	return -1;
	//return -2;
}

int  f_llegadaB_SigAjuste(HCoche hc)
{/*
	int i, j, l, pos, pos2, k, contarCerosAntes, contarCerosDespues, contarCerosGuille;
	static int ultimoOcupado = 0;
	int longitud = PARKING2_getLongitud(hc);
	char temp;
	//Caso raro, en caso que el ultimo coche que aparcO ya se haya ido entonces miramos si el hueco que dejO ahI
	//puede entrar el nuevo coche(por hueco que dejO me refiero al hueco que ocupaba mAs algUn hueco desaprovechado que pudiese haber

	if (ID_memptr[ultimoOcupado + OFFT_SIGAJUSTE] == LIBRE)
	{
	contarCerosGuille = 0;
	l = ultimoOcupado;
	// l > 0 para que no valga -1 y ultimo ocupado funcione desde 0
	while (l > 0 && ID_memptr[l + OFFT_SIGAJUSTE] == LIBRE)
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
	while (j < TAM_ACERA && ID_memptr[j + OFFT_SIGAJUSTE] == LIBRE)
	{
	contarCerosDespues++;
	j++;
	}
	if (contarCerosDespues >= longitud)
	{
	for (k = pos; k < pos + longitud; k++)
	{
	ID_memptr[k + OFFT_SIGAJUSTE] = RESERVADA;
	
	}
	ultimoOcupado = pos + longitud - 1;
	CreateThread(NULL, 0, preAparcarSig, &hc, 0, NULL);
	WaitForSingleObject(preaparcarSigAjuste, INFINITE);
	return pos;
	}
	}
	//Empieza de nuevo
	for (i = 0; i < ultimoOcupado; i++)
	{
	pos2 = j = i;
	contarCerosAntes = 0;
	while (j < TAM_ACERA && ID_memptr[j + OFFT_SIGAJUSTE] == LIBRE)
	{
	contarCerosAntes++;
	j++;
	}
	if (contarCerosAntes >= longitud)
	{
	for (k = pos2; k < pos2 + longitud; k++)
	{
	ID_memptr[k + OFFT_SIGAJUSTE]= RESERVADA;
	
	}
	ultimoOcupado = pos2 + longitud - 1;
	CreateThread(NULL, 0, preAparcarSig, &hc, 0, NULL);
	WaitForSingleObject(preaparcarSigAjuste, INFINITE);
	return pos2;
	}
	}
	return -1;*/
	return -2;
}

int  f_llegadaC_MejorAjuste(HCoche hc)
{/*
	char temp;
	int longitud = PARKING2_getLongitud(hc);
	
	int menor, posInicial, posFinal, contarCeros, i, j, pos;
	menor = TAM_ACERA + 1;
	posInicial = -1;
	posFinal = -1;

	for (i = 0; i < TAM_ACERA;)
	{
	contarCeros = 0;
	if (ID_memptr[i + OFFT_MEJORAJUSTE] == LIBRE)
	{
	pos = j = i;
	while (j < TAM_ACERA && ID_memptr[j + OFFT_MEJORAJUSTE] == LIBRE)
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
	ID_memptr[i + OFFT_MEJORAJUSTE] = RESERVADA;
	}
	}
	CreateThread(NULL, 0, preAparcarM, &hc, 0, NULL);
	WaitForSingleObject(preaparcarMejAjuste, INFINITE);
	return posInicial;
	*/
	return -2;
}

int f_llegadaD_PeorAjuste(HCoche hc)
{
	/*int mayor, posInicial, posFinal, i, j, contarCeros, pos;
	int longitud = PARKING2_getLongitud(hc);
	char temp;
	mayor = -1;
	posInicial = -1;
	posFinal = -1;

	for (i = 0; i < TAM_ACERA;)
	{
	contarCeros = 0;
	if (ID_memptr[i + OFFT_PEORAJUSTE] == LIBRE)
	{
	pos = j = i;
	while (j < TAM_ACERA && ID_memptr[j + OFFT_PEORAJUSTE] == LIBRE)
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
	temp = RESERVADA;
	CopyMemory(ID_memptr + i + OFFT_PEORAJUSTE, &temp, sizeof(char));
	}
	}
	return posInicial;*/
	return -2;
}

void aparcar_commit(HCoche hc){
	int numCoche = PARKING2_getNUmero(hc);
	int algoritmo = PARKING2_getAlgoritmo(hc);
	if (algoritmo == PRIMER_AJUSTE) {
		doSignalPrim(numCoche + 1);
	}

}

void permiso_avance(HCoche hc)
{
	int off, sem;
	int i, valido = 1;
	int longCoche = PARKING2_getLongitud(hc);
	int posIrX = PARKING2_getX2(hc);
	int posIrY = PARKING2_getY2(hc);
	int posEstaX = PARKING2_getX(hc);
	int posEstaY = PARKING2_getY(hc);
	char temp;

	if ((PARKING2_getAlgoritmo(hc)) == MEJOR_AJUSTE)
	{
		sem = SEM_MEJORAJUSTE;
		off = OFFT_MEJORAJUSTE;
		
	}
	else if ((PARKING2_getAlgoritmo(hc)) == PEOR_AJUSTE)
	{
		sem = SEM_PEORAJUSTE;
		off = OFFT_PEORAJUSTE;
	}
	else if ((PARKING2_getAlgoritmo(hc)) == SIGUIENTE_AJUSTE)
	{
		sem = SEM_SIGUAJUSTE;
		off = OFFT_SIGAJUSTE;
	}
	else if ((PARKING2_getAlgoritmo(hc)) == PRIMER_AJUSTE)
	{
		sem = SEM_PRIMRAJUSTE;
		off = OFFT_PRIMRAJUSTE;
	}
	//linea-parking o parking-linea o carretera-linea
	if (posIrY == LINEA && posEstaY == PARKING) //de parking a linea
	{
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posIrX + i + OFFT_LINEA + off] = OCUPADA;
		

		}
	}
	else if (posIrY == PARKING && posEstaY == LINEA) //linea-parking
	{
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posIrX + i + OFFT_PARKING + off] = OCUPADA;
			

		}
	}
	else if (posIrY == LINEA && posEstaY == CARRETERA) //road-linea
	{
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posIrX + i + OFFT_LINEA + off]= OCUPADA;
			

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
		//printf("wait del semaforo %d\n", posIrX + sem);
		doWait(posIrX  + sem);
		ID_memptr[posIrX + OFFT_CARRETERA + off]= OCUPADA;
		

	}
	else if (posIrY == CARRETERA && posEstaY == LINEA) //de linea a road
	{
		//!! OJO !! del culo -> morro
		for (i = longCoche - 1; i >= 0; i--)
		{
			doWait(posIrX + i + sem);
			ID_memptr[posIrX + i + OFFT_CARRETERA + off] = OCUPADA;
			

		}
	}
}


void permiso_avance_commit(HCoche hc)
{
	int longCoche = PARKING2_getLongitud(hc);
	int posVeniaX = PARKING2_getX2(hc);
	int posVeniaY = PARKING2_getY2(hc);
	int posEstaX = PARKING2_getX(hc);
	int posEstaY = PARKING2_getY(hc);
	int off, sem, i;
	char temp;

	if ((PARKING2_getAlgoritmo(hc)) == MEJOR_AJUSTE)
	{
		sem = SEM_MEJORAJUSTE;
		off = OFFT_MEJORAJUSTE;
	}
	else if ((PARKING2_getAlgoritmo(hc)) == PEOR_AJUSTE)
	{
		sem = SEM_PEORAJUSTE;
		off = OFFT_PEORAJUSTE;
	}
	else if ((PARKING2_getAlgoritmo(hc)) == SIGUIENTE_AJUSTE)
	{
		sem = SEM_SIGUAJUSTE;
		off = OFFT_SIGAJUSTE;
	}
	else if ((PARKING2_getAlgoritmo(hc)) == PRIMER_AJUSTE)
	{
		sem = SEM_PRIMRAJUSTE;
		off = OFFT_PRIMRAJUSTE;
	}
	if (posVeniaY == LINEA && posEstaY == CARRETERA) //de linea a road
	{
		// Libero linea
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posVeniaX + i + OFFT_LINEA + off] = LIBRE;
			

		}
		// Libero parking
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posVeniaX + i + OFFT_PARKING + off]= LIBRE;
			

		}
	}
	else if (posVeniaY == CARRETERA && posEstaY == LINEA) //de road a linea
	{
		//Libero carretera
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posVeniaX + i + OFFT_CARRETERA + off]= LIBRE;
			
			doSignal(posVeniaX + i + sem);
		}
	}
	else if (posVeniaY == LINEA && posEstaY == PARKING) //de linea a parking
	{
		//libero linea
		for (i = 0; i < longCoche; i++)
		{
			ID_memptr[posVeniaX + i + OFFT_LINEA + off]= LIBRE;
			

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
			ID_memptr[posVeniaX + longCoche - 1 + OFFT_CARRETERA + off] = LIBRE;
			
			doSignal(posVeniaX + longCoche - 1  + sem);
		}
	}
}




void iniciar_Aceras()
{
	int i;
	char temp;
	//PARA ZONA APARCAR + LINEA DISCONTINUA + CARRETERA * 4 Algoritmos
	for (i = 0; i < tamMem; i++)
	{
		ID_memptr[i] = LIBRE;
	}
}

HINSTANCE controladorDLL;

int main(int argc, char *argv[])
{
	//un puntero para cada funcion el puntero debe ser del mismo tipo que el tipo devuelto por la funciOn tiene que ser asI para todas las funciones que vengan en el .h y utilicemos
	
	//Cargar biblioteca
	controladorDLL = LoadLibrary("parking2.dll");
	//Enlazado
	PARKING2_inicio = (int(*)(TIPO_FUNCION_LLEGADA *, TIPO_FUNCION_SALIDA *, LONG, BOOL))GetProcAddress(controladorDLL, "PARKING2_inicio");
	PARKING2_aparcar = (int(*)(HCoche, void *datos, TIPO_FUNCION_APARCAR_COMMIT, TIPO_FUNCION_PERMISO_AVANCE, TIPO_FUNCION_PERMISO_AVANCE_COMMIT))GetProcAddress(controladorDLL, "PARKING2_aparcar");
	PARKING2_desaparcar = (int(*)(HCoche, void *datos, TIPO_FUNCION_PERMISO_AVANCE, TIPO_FUNCION_PERMISO_AVANCE_COMMIT)) GetProcAddress(controladorDLL, "PARKING2_desaparcar");
	PARKING2_getNUmero = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getNUmero");
	PARKING2_getLongitud = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getLongitud");
	PARKING2_getPosiciOnEnAcera = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getPosiciOnEnAcera");
	PARKING2_getTServ = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getTServ");
	PARKING2_getDatos = (void(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getDatos");
	PARKING2_getX = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getX");
	PARKING2_getY = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getY");
	PARKING2_getX2 = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getX2");
	PARKING2_getY2 = (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getY2");
	PARKING2_fin = GetProcAddress(controladorDLL, "PARKING2_fin");
	PARKING2_getAlgoritmo= (int(*)(HCoche)) GetProcAddress(controladorDLL, "PARKING2_getAlgoritmo");


	/*if ((!validar_parametros(argc, argv)))
	{
		printf(" Debe introducir entre dos y tres argumentos de la siguiente forma:\n");
		printf("\tENTERO >= 0 (representa la rapidez con la que ocurren los acontecimientos => 0\n");
		printf("\trapidez maxima, cuanto mayor el numero menor rapidez\n");
		printf("\tNUM_CHOFERES > 0\n");
		printf("\tD (para activar el modo con depuracion\n\n");
		return 1;
	}*/
	
	int numSem = (4 * TAM_ACERA);
	
	int i;
	tamMem = (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char)) + (TAM_ACERA * NUM_ACERAS * sizeof(char)); //+ (atoi(argv[2]) + 1) * sizeof(int));
	ID_memptr = (char *)malloc(tamMem * sizeof(char));
	iniciar_Aceras();
	
	ID_semaforo = (HANDLE *)malloc(numSem * sizeof(HANDLE));
	semaforos_primer = (HANDLE *)malloc(30000 * sizeof(HANDLE));
	semaforos_sig= (HANDLE *)malloc(30000 * sizeof(HANDLE));
	semaforos_mejor = (HANDLE *)malloc(30000 * sizeof(HANDLE));
	semaforos_peor = (HANDLE *)malloc(30000 * sizeof(HANDLE));
	
	for (i = 0; i < numSem; i++)
	{
		ID_semaforo[i] = crea_semaforo();
	}
	//ID_mem = crea_memoria_compartida(tamMem);
	//ID_memptr = crea_punteroChar(ID_mem);
	semaforos_primer[1]= crea_semaforo();
	semaforos_sig[1] = crea_semaforo();
	semaforos_mejor[1] = crea_semaforo();
	semaforos_peor[1] = crea_semaforo();
	for (i = 2; i < 30000; i++)
	{
		semaforos_primer[i] = crea_semaforo2();
		semaforos_sig[i] = crea_semaforo2();
		semaforos_mejor[i] = crea_semaforo2();
		semaforos_peor[i] = crea_semaforo2();
	}

	sem_MEJORAJUSTE = crea_semaforo();
	sem_PEORAJUSTE = crea_semaforo();
	sem_PRIMAJUSTE = crea_semaforo();
	sem_SIGAJUSTE = crea_semaforo();
	

	PARKING2_inicio(f_llegadas, f_salidas, 3, 0);
	while (666) {

	}
	
	getchar();
	return 0;
}

//Semaforo
HANDLE WINAPI crea_semaforo()
{
	HANDLE semaforo;
	semaforo = CreateSemaphore(NULL, 1, 1, NULL);
	if (semaforo == NULL)
	{
		perror(NULL);
	error("Error al crear semaforo");
		exit(1);
	}
	return semaforo;
}
HANDLE WINAPI crea_semaforo2()
{
	HANDLE semaforo;
	semaforo = CreateSemaphore(NULL, 0, 1, NULL);
	if (semaforo == NULL)
	{
		perror(NULL);
		error("Error al crear semaforo");
		exit(1);
	}
	return semaforo;
}
void error(const char *errorInfo)
{
	fprintf(stderr, "%s\n", errorInfo);
}

void doSignal(int numSem)
{
	BOOL signal = ReleaseSemaphore(ID_semaforo[numSem], 1, NULL);
	/*if (signal == 0)
	{
		perror(NULL);
		error("Error al hacer signal");
		exit(1);
	}*/
}
void doSignalPrim(int numSem)
{
	BOOL signal = ReleaseSemaphore(semaforos_primer[numSem], 1, NULL);
	/*if (signal == 0)
	{
	perror(NULL);
	error("Error al hacer signal");
	exit(1);
	}*/
}
void doWait(int numSem)
{
	DWORD signal = WaitForSingleObject(ID_semaforo[numSem], INFINITE);
	/*if (signal == 0)
	{
		perror(NULL);
		error("Error al hacer wait");
		exit(1);
	}*/
}
void doWaitPrim(int numSem)
{
	DWORD signal = WaitForSingleObject(semaforos_primer[numSem], INFINITE);
	/*if (signal == 0)
	{
	perror(NULL);
	error("Error al hacer wait");
	exit(1);
	}*/
}

//Parametros
int WINAPI validar_parametros(int argc, char *argv[])
{
	if (argc < 2 || argc > 3)
	{
		return 0;
	}

	if (argc == 3)
	{
		if ((atoi(argv[1])) < 0 || (strcmp(argv[2], "D") != 0))
		{
			return 0;
		}
		return 1;
	}
	return 0;
}

//Memoria compartida
HANDLE WINAPI crea_memoria_compartida(size_t tam) {
	HANDLE mem;
	mem = CreateFileMapping(NULL, NULL, PAGE_READWRITE, 0, tam, "MemoriaCompartida");  //HANDLE DE LA MEMORIA COMPARTIDA
																					   //Capturar errores
	return mem;
}

char * WINAPI crea_punteroChar(HANDLE memoria) {
	char *temp;
	temp = (char *)MapViewOfFile(memoria, FILE_MAP_ALL_ACCESS, 0, 0, sizeof(char)); //PUNTERO A MEMORIA COMPARTIDA
																					//capturar errores
	return temp;
}

