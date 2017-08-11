#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <strings.h>
#include <ctype.h>

#define MAX_SAVED_MIN_DEMERITS 	30000				
#define MAX_SAVED_SPM_PRES 		10000 			/* Note! Must have MAX_SAVED_SPM_PRES <= MAX_SAVED_PRES. */
#define MAXTRIALSWOUPDATE   	1000000
#define	SPM_INFINITE			2000000000

unsigned char	**SaveDualRelators[MAXNUMRELATORS + 1],
				**SaveRelators[MAXNUMRELATORS + 1];
	
int 			C1,
				C2,
				C3,
				C4,
				*DeMerits,
				MaxDeMerits,
				MaxDeMeritsLoc,
				MinDeMerits,
				MinDeMeritsLoc,
				MyNumGens,
				MyNumRels,
				NumPrim1,
				NumPrim2,
				NumPairsSepVerts2,
				*SPM_Depth;		
							 
unsigned int	Word;

unsigned long	Delta,
				NumTrials 	= 0,
				NumUpDates  = 0;
	
FILE			*fptr,
				*MyOut;

/******************************* Functions in Heegaard23.c ********************************
L 704 SPM_Compare_Pres_SUR(int)
L 812 SPM_ComputeDeMerits(char)
L 893 SPM_Count_Primitives(void)
L 384 SPM_Do_Initialization(void)
L 400 SPM_Free_Storage(void)
L 417 SPM_Get_Diagrams(void)
L  78 SPM_Get_Initial_Values_From_User(void)
L 343 SPM_Input_Form_Warning(char)
L 790 SPM_LocateMaxDeMerits(void)
L  56 SPM_main(void)
L 369 SPM_On_File(void)
L 149 SPM_Read_PM_Data(void)
L 949 SPM_Sep_Pairs(int,int,int)
L 731 SPM_SetUpInitialDemerits(void)
********************************************************************************************/	

int SPM_main(void)
{
				
	SPM_Do_Initialization();
	
	if(SPM_Get_Initial_Values_From_User()) 
		{
		SPM_Free_Storage();
		return(1);
		}		
	
	SPM_SetUpInitialDemerits();
	
	SPM_Get_Diagrams();
	
	SPM_Free_Storage();
	
	printf("\n\nFinished searching!.\n");
		
	return(0);			
}		

int SPM_Get_Initial_Values_From_User(void)
{
	fptr = fopen("Heegaard_Input_SPM_Presentations","r+");	
	if(fptr == NULL)
		{
      	SysBeep(5);
        printf("\nUnable to open the file 'Heegaard_Input_SPM_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_SPM_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        return(1);		
		}

	if(SPM_Read_PM_Data()) return(1);
		
	NumRelators   	= NumGenerators;
	ReadPres		= 0;
	Vertices 		= 2*NumGenerators;
	MyNumGens = NumGenerators;
	MyNumRels = NumRelators;
	
	printf("\n\nENTER VALUES BETWEEN 0 AND 1,000 FOR PARAMETERS C1, C2, C3, AND C4 HEEGAARD SHOULD USE TO COMPUTE DEMERITS.");   
 	printf("\nHeegaard uses: DeMerits = C1*(|R| - |DR|) + C2*|Primitives(R)| + C3*|Primitives(DR)| + C4*|SepVertPairs(DR)|");
 	printf("\nWhere |R| = Min Length of Relators, |DR| = Min Length of DualRelators, |Primitives(R)| = Num of primitive R relators,");
 	printf("|Primitives(DR)| = Num of primitive DualRelators, and |SepVertPairs(DR)| is 1 or 0 depending upon whether there are pairs");
 	printf(" of separating vertices in the Whitehead graph of the DualRelators.\n");
 	
	GET_RESPONSE1:
	printf("\n\nPlease enter C1:	");	  
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%u",&C1); 
	if(C1 < 0 || C1 > 1000)
		{   	
		SysBeep(5);
		printf("\nC1 is out of range.");
		goto GET_RESPONSE1;
		}
	GET_RESPONSE2:
	printf("\n\nPlease enter C2:	");	
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%u",&C2); 
	if(C2 < 0 || C2 > 1000)
		{   	
		SysBeep(5);
		printf("\nC2 is out of range.");
		goto GET_RESPONSE2;
		}			
	GET_RESPONSE3:
	printf("\n\nPlease enter C3:	");	  
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%u",&C3); 
	if(C3 < 0 || C3 > 1000)
		{   	
		SysBeep(5);
		printf("\nC3 is out of range.");
		goto GET_RESPONSE3;
		}
	GET_RESPONSE4:
	printf("\n\nPlease enter C4:	");	  
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%u",&C4); 
	if(C4 < 0 || C4 > 1000)
		{   	
		SysBeep(5);
		printf("\nC4 is out of range.");
		goto GET_RESPONSE4;
		}
	printf("\n(C1,C2,C3,C4) = (%d,%d,%d,%d) ",C1,C2,C3,C4);	
					
	return(0);	
}

int SPM_Read_PM_Data(void)
{
	unsigned char	*p,
					*q,
					t;
	
	int				j,
					MyNumGens;
						
	unsigned int 	h,
					i;
	
	fptr = fopen("Heegaard_Input_SPM_Presentations","r");	
	if(fptr == NULL)
		{
      	SysBeep(5);
        printf("\nUnable to open the file 'Heegaard_Input_SPM_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_SPM_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        goto END;		
		}

	NumFilled = 0;
		
	while(1)
		{
NEXT_PRES:
		
		/**************************************************************************************
				1)	Look for a line whose initial character is a digit.
		**************************************************************************************/
			
		do
			{
			if(fgets((char *) PresName,MAXLENGTH,fptr) == NULL)
				goto END;
			}
		while(!isdigit(*PresName));
		
		/**************************************************************************************
				2) 	Look for the next nonempty line.
		**************************************************************************************/
			
		do
			{
			if(fgets((char *) Inst,MAXLENGTH,fptr) == NULL)
				goto END;
			}
		while(*Inst == '\n' || *Inst == '\r');
		
		/**************************************************************************************
				3)	Read in the relators at one relator to each nonempty line.
		**************************************************************************************/	
					
		for(i = 1,NumRelators = 0; i <= MAXNUMRELATORS; i++)
			{
			while(1)
				{
				p = Inst;
				t = *p;
				h = 0;
				while(t == ' ' || t == '\t')
					{
					h++;
					p++;
					t = *p;
					}
				if(t == '\n' || t == EOS)
					{
					*p = EOS;
					goto NEXT_PRES;
					}	
				while(1)
					{
					t = *p;
					if(t == EOS || t == '\n' || t == ' ' || t == '\t')
						{
						*p = EOS;
						goto READ_RELATOR;
						}	
					if(!isalpha(t))
						{
						printf("\n\nCheck relator %u of %s ",i,PresName);						
						printf("\nA relator can only contain upper and lower case letters!");
						printf("\nMake sure each relator is on its own line!");
						printf("\nAnd the presentation is terminated by an empty line!");
						goto NEXT_PRES;
						}
					p++;		
					}								
				}
	READ_RELATOR:
				
			if(*Inst == '\n') break;
			Length = p - Inst;
			if(Length == h) break;
			if(Length >= MAXLENGTH)
				{
				SysBeep(5);
				printf("\n\nA relator has length > %u, which is too long!",MAXLENGTH);
				fclose(fptr);
				return(1);
				}
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle((Size)(Length + 1 - h));
			if(Relators[i] == NULL) Mem_Error();
			p = *Relators[i];
			q = Inst + h;
			while( (*p++ = *q++) ) ;
			NumRelators ++;
			
			if(fgets((char *) Inst,MAXLENGTH,fptr) == NULL) break;
			if(*Inst == '\n') break;
			}
			
		for(i = 1, Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
		Length -= NumRelators;
		j = Freely_Reduce();
		NumRelators -= j;
		Length = OrigLength;
		Rewrite_Input();
		if((NumRelators != NumGenerators) || NumGenerators < 2)
			{ 
			SPM_Input_Form_Warning(1);
			Print_Relators(Relators,NumRelators);
			fclose(fptr);
			fptr = NULL;
			return(1);
			}
		Vertices = 2*NumGenerators;	
		if(Find_Flow_A(NORMAL,0))
			{
			SPM_Input_Form_Warning(2);
			Print_Relators(Relators,NumRelators);
			fclose(fptr);
			fptr = NULL;
			return(1);			
			}
		if(Whitehead_Graph())
			{
			SPM_Input_Form_Warning(3);
			Print_Relators(Relators,NumRelators);
			continue;
			}
		if(Sep_Surface() > 1)
			{
			SPM_Input_Form_Warning(4);
			Print_Relators(Relators,NumRelators);
			fclose(fptr);
			fptr = NULL;
			return(1);			
			}
		if(NumFilled == 0) MyNumGens = NumGenerators;
		if(NumGenerators != MyNumGens) 
			{
			SPM_Input_Form_Warning(5);
			Print_Relators(Relators,NumRelators);
			continue;
			}		
		Canonical_Rewrite(Relators,FALSE,FALSE);
			
		if(SPM_On_File() == NumFilled)
			{	
			for(i = 1; i <= NumRelators; i++)
				{
				if(SUR[NumFilled][i] != NULL) DisposeHandle((char **) SUR[NumFilled][i]);
				SUR[NumFilled][i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
				if(SUR[NumFilled][i] == NULL) Mem_Error();
				p = *Relators[i];
				q = *SUR[NumFilled][i];	
				while( (*q++ = *p++) ) ;
				}
			SURL[NumFilled] = Length;
			NG[NumFilled] = NumGenerators;
			NR[NumFilled] = NumRelators;
			UDV[NumFilled] = 0;
			NumFilled ++;		
			if(NumFilled >= MAX_SAVED_SPM_PRES) goto END;
			}			
		}
		
END:
	if(fptr)
		fclose(fptr);
	fptr = NULL;	
	if(NumFilled == 0)
		{
		printf("\n\nNote that Heegaard's SPM_Routine() expect the label of each presentation in 'Heegaard_Input_SPM_Presentations'\n");
		printf("to begin with a digit. In particular, no initial spaces or tabs in the label.");
		return(1);
		}
	return(0);	
}

void SPM_Input_Form_Warning(char flag)
{
	switch(flag)
		{
		case 1:
			printf("\n\nHeegaard's SPM_Routine() expects presentations in 'Heegaard_Input_SPM_Presentations' to be balanced, realizable\n");
			printf("presentations of Heegaard splittings of a closed manifold, all of which have the same genus.");
			break;
		case 2:
			printf("\n\nAutomorphisms disclosed a problem. Perhaps a missing generator in the following presentation.");
			break;	
		case 3:
			printf("\n\nHeegaard's SPM_Routine() expects presentations in 'Heegaard_Input_SPM_Presentations' to be balanced, realizable\n");
			printf("presentations whose Whitehead graphs are connected and have no separating pairs of vertices.");
			break;
		case 4:
			printf("\n\nHeegaard's SPM_Routine() doesn't think the following presentation in 'Heegaard_Input_SPM_Presentations' is a\n");
			printf("presentation of a closed manifold.");
			break;
		case 5:
			printf("\nSkipping the following presentation. Heegaard's SPM_Routine() expects all of the presentations in\n");
			printf("'Heegaard_Input_SPM_Presentations' to have the same number of generators.");
			break;
		}
}

unsigned int SPM_On_File(void)
{
	int		i,
			j;
			
	for(i = 0; i < NumFilled; i++)
    if(SURL[i] == Length && NG[i] == NumGenerators && NR[i] == NumRelators)
        {
         for(j = 1; j <= NumRelators; j++)
             if(GetHandleSize((char **) Relators[j]) != GetHandleSize((char **) SUR[i][j])) break;
         if(j > NumRelators && Compare_Pres(i)) break;    
        }       
    return(i);    
}	

void SPM_Do_Initialization(void)
{
	unsigned int 	i;
			
	DeMerits		= (int*) NewPtr(sizeof(int)*(MAX_SAVED_SPM_PRES + 1));
	if(DeMerits 	== NULL) Mem_Error();
	SPM_Depth		= (int*) NewPtr(sizeof(int)*(MAX_SAVED_SPM_PRES + 1));
	if(SPM_Depth 	== NULL) Mem_Error();
								
	for(i = 0; i <= MAXNUMRELATORS; i++)
		{
		SaveRelators[i] = NULL;
		SaveDualRelators[i] = NULL;
		}		
}

void SPM_Free_Storage(void)
{
	if(DeMerits)  DisposePtr((int*) DeMerits);
	if(SPM_Depth) DisposePtr((int*) SPM_Depth);
	if(fptr) 
		{
		fclose(fptr);
		fptr = NULL;
		}
	if(MyOut) 
		{
		fflush(MyOut);
		fclose(MyOut);
		MyOut = NULL;
		}
}

int SPM_Get_Diagrams(void)
{
	unsigned char	*p,
					*q,
					Retries,
					**Temp;
					
	int 			DeMerit,
					Depth,
					i,
					k,
					NumTries;
					
	unsigned int	MyNumAutomorphisms,
					MyNumBandSums,
					NumBandSums,
					NumEvaluated,
					NumMinDeMerits;									
					
	unsigned long	LastUpDate,
					MySLength,
					NumTrials,
					NumUpDates,
					SSLength,
					SSSLength,
					TotalBandSums;												

	LastUpDate			= 0;
	MinDeMerits 		= SPM_INFINITE;
	NumEvaluated		= 0;
	NumMinDeMerits		= 0;
	NumTrials 			= 0;
	NumUpDates 			= 0;	
	ReadPres 			= 0,
	Retries				= TRUE;
	TotalBandSums 		= 0;
	
	for(i = 0; i < NumFilled; i++) SPM_Depth[i] = 0;
	
	SPM_LocateMaxDeMerits();
	
	printf("\n\nNumFilled %u, Initial MinDeMerits %d, MaxDeMerits %d ",NumFilled,MinDeMerits,MaxDeMerits);	
	
	if(MyOut != NULL) fprintf(MyOut,"\n\nNumFilled %u, Initial MinDeMerits %d, MaxDeMerits %d  ",NumFilled,MinDeMerits,MaxDeMerits);	
	
	while(1)
		{		
		if(mykbhit()) 
			{ 
			printf("\n\nWAITING!! \nHIT 'q' TO 'quit'.");
			printf("\nHIT 's' TO GET A STATUS REPORT AND CONTINUE.    ");
			switch(WaitkbHit())
				{
				case 's':
					printf("\n\nNumTrials %lu, Bandsums %lu, NumEvaluated %u, NumUpDates %lu, NumFilled %u, MaxDeMerits %d, ",
						NumTrials,TotalBandSums,NumEvaluated,NumUpDates,NumFilled + 1,MaxDeMerits);
					printf("Trials since last update %lu",NumTrials - LastUpDate);
					break;	
				case 'q':
					return(0);	
				}
			}
		if(NumTrials - LastUpDate > MAXTRIALSWOUPDATE)
			{
			printf("\n\nStopping. There have been more than %d trials without an update.", MAXTRIALSWOUPDATE);
			return(0);
			}			
		NumGenerators 	= NG[ReadPres];
		NumRelators 	= NR[ReadPres];
		Vertices 		= 2*NumGenerators;
		UDV[ReadPres] ++;
		if(UDV[ReadPres] >= Vertices) UDV[ReadPres] = 0;
		for(i = 1; i <= NumRelators; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(Relators[i] == NULL) Mem_Error();
			p = *Relators[i];
			q = *SUR[ReadPres][i];
			while( (*p++ = *q++)) ;	
			}			
		Length = SURL[ReadPres];		
		NumTrials ++;
		NumTries = 0;		
		Fill_A(NumRelators);
		if(Whitehead_Graph())
			{
			DeMerits[ReadPres] = SPM_INFINITE;
			goto NEXT_PRES;
			}
		MyNumAutomorphisms = 0;
		MyNumBandSums = 0;	
		NumBandSums = 0;					
		while(1)
			{
RETRY:								
			/*******************************************************************************************
				Form repeated bandsums until: 1) The presentation becomes too long, or 2) A presentation
				with a "bad" Whitehead graph is generated, or 3) A presentation P, which does not have
				minimal length and has a "good" Whitehead graph is generated.
			********************************************************************************************/

			GoingUp 	= TRUE;
			GoingDown 	= FALSE;
			for(i = 0,Minimum = BIG_NUMBER; Minimum == BIG_NUMBER && i < 5; i++) New_Relator(TRUE);
			if(Minimum == BIG_NUMBER) goto NEXT_PRES;
			if(Minimum < BIG_NUMBER)
				{
				if(abs(rand()) % 2) 
					Word = Word1;
				else
					Word = Word2;	
				LR[0] = GetHandleSize((char **) OutRelators[Word]) - 1;
				i = Word;
				Word = abs(Compare(*OutRelators[i]));
				if(Word == 0)
					{
					SysBeep(5);
					printf("\n\nError in forming a bandsum. Relators are probably too long.");
					goto NEXT_PRES;
					}		
				Temp 			= Temp3;
				Temp3 			= Relators[Word];	
				Relators[Word] 	= Relators[1];
				Relators[1] 	= Temp2;
				Temp2 			= Temp;		
				for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
				Length -= NumRelators;
				MySLength = SSLength = Length;
				if(Find_Flow_A(BANDSUM,0)) goto NEXT_PRES;
				MyNumAutomorphisms += Automorphisms;				
				SSSLength = Length;	
				if(Whitehead_Graph()) goto NEXT_PRES;
				MyNumBandSums 	++;
				NumBandSums  	++;								
				if(SSLength > SSSLength) goto EVALUATE;						
				}				
			}
						
		/*******************************************************************************************
				If P's DeMerits are smaller than MaxDeMerits and P is not on file in SUR, replace 
			the presentation currently in SUR at MaxDeMeritsLoc with P. Update MaxDeMerits. 
			If MaxDeMerits = 0, print results and quit.
				If P's DeMerits are equal or larger than MaxDeMerits, or P is on file in SUR, 
			goto NEXT_PRES.
				Otherwise, if P's dual presentation is not on file, has a "good" Whitehead graph, 
			and has DeMerits smaller than MaxDeMerits, replace the presentation in SUR at 
			MaxDeMeritsLoc with P's dual. Continue checking further dual presentations.
		**********************************************************************************************/
EVALUATE:
		TotalBandSums += NumBandSums;
		Depth = 0;
		while(1)
			{									
			if(SPM_LocateMaxDeMerits() == -1)
				{
				printf("\n\nMaxDeMerits = 0.");
				return(0);
				}
			DeMerit = SPM_ComputeDeMerits(FALSE);					
			if(DeMerit == -1) goto NEXT_PRES;								
			if(MaxDeMerits == 0)
				{
				printf("\n\nMaxDeMerits = 0.");
				return(0);
				}
			if(Retries && DeMerit >= MaxDeMerits && NumTries++ < 3) 
				{
				Fill_A(NumRelators);
				if(Whitehead_Graph()) goto NEXT_PRES;
				goto RETRY;	
				}
			NumEvaluated ++;	
			if(DeMerit < MaxDeMerits)
				{				
				for(i = 1,Length = 0; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SaveRelators[i]));
					if(Relators[i] == NULL) Mem_Error();
					Length += GetHandleSize((char **) Relators[i]);
					p = *Relators[i];
					q = *SaveRelators[i];
					while( (*p++ = *q++)) ;						
					}
				Length -= NumRelators;	
				Canonical_Rewrite(Relators,FALSE,FALSE);				
				if(SPM_On_File() < NumFilled) goto NEXT_PRES;				
				k = MaxDeMeritsLoc;
				for(i = 1; i <= NumRelators; i++)
					{
					if(SUR[k][i] != NULL) DisposeHandle((char **) SUR[k][i]);
					SUR[k][i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
					if(SUR[k][i] == NULL) Mem_Error();
					p = *SUR[k][i];
					q = *Relators[i];
					while( (*p++ = *q++)) ;
					}
				SURL[k] 		= Length;
				NG[k] 			= NumGenerators;
				NR[k] 			= NumRelators;
				UDV[k] 			= 0;
				DeMerits[k] 	= DeMerit;
				SPM_Depth[k] 	= Depth;
				NumUpDates 		++;
				LastUpDate		= NumTrials;				
				if(k > NumFilled && NumFilled < MAX_SAVED_SPM_PRES) NumFilled ++;
				if(DeMerit <= MinDeMerits || DeMerit == 0)
					{
					NumMinDeMerits ++;
					if(NumMinDeMerits >= MAX_SAVED_MIN_DEMERITS)
						{
						printf("\n\nNumMinDeMerits >= the preset limit %d = MAX_SAVED_MIN_DEMERITS.",MAX_SAVED_MIN_DEMERITS);
						return(0);
						}
        			printf("\n\n%d) At Trial %lu, NumEvaluated %u: Started from presentation %d, Length %lu, DeMerits %d:",
        				NumMinDeMerits,NumTrials,NumEvaluated,ReadPres,SURL[ReadPres],DeMerits[ReadPres]);
        			for(i = 1; i <= NR[ReadPres]; i++) printf("\n    %s",*SUR[ReadPres][i]);
        			if(NumTries)
       					printf("\n\n%da) After %d Tries, totals of %u BandSum(s) and %u Automorphisms, Heegaard found: ",
 							NumMinDeMerits,NumTries + 1,MyNumBandSums,MyNumAutomorphisms);		
 					else
 						printf("\n\n%da) After %u BandSum(s) Length equaled %lu. Then %u Automorphism(s) gave: ",
 							NumMinDeMerits,MyNumBandSums,MySLength,MyNumAutomorphisms);		
					if(SPM_Depth[k])
						printf("Length %lu, DeMerits %d, after %d dualization(s), ",SURL[k],DeMerit,SPM_Depth[k]);
					else 
						printf("Length %lu, DeMerits %d, ",SURL[k],DeMerit);
        			printf("( %lu, %d, %d, %d ) ",Delta,NumPrim1,NumPrim2,NumPairsSepVerts2);
        			if(Retries == FALSE && NumPrim1 == 0 && NumPrim2 == 0 && NumPairsSepVerts2 == 0) Retries = TRUE;
        			for(i = 1; i <= NR[k]; i++) printf("\n    %s",*SUR[k][i]);
        			if(MyOut != NULL)
        				{
        				if(SPM_Depth[k])
        					fprintf(MyOut,"\n\n%d) At Trial %lu, NumEvaluated %u: Length %lu, DeMerits %d, after %d dualization(s) ",
        						NumMinDeMerits,NumTrials,NumEvaluated,SURL[k],DeMerit,SPM_Depth[k]);
        				else	
        					fprintf(MyOut,"\n\n%d) At Trial %lu, NumEvaluated %u: Length %lu, DeMerits %d, ",
        						NumMinDeMerits,NumTrials,NumEvaluated,SURL[k],DeMerit);
        				fprintf(MyOut,"( %lu, %d, %d, %d ) ",Delta,NumPrim1,NumPrim2,NumPairsSepVerts2);
        				for(i = 1; i <= NR[k]; i++) fprintf(MyOut,"\n    %s",*SUR[k][i]);
        				fflush(MyOut);
        				}			
					}
					
				/**********************************************************************************
											Check the DualRelators.
				***********************************************************************************/
			
				for(i = 1; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SaveDualRelators[i]));
					if(Relators[i] == NULL) Mem_Error();
					p = *Relators[i];
					q = *SaveDualRelators[i];
					while( (*p++ = *q++)) ;						
					}
					
				for(i = 1; i <= NumRelators; i++)
					{
					Temp = SaveRelators[i];
					SaveRelators[i] = SaveDualRelators[i];
					SaveDualRelators[i] = Temp;				
					}	
			
				MyNumGens = NumGenerators;
				MyNumRels = NumRelators;
				Rewrite_Input();
				if(NumGenerators < MyNumGens) goto NEXT_PRES;	
				if(NumRelators < MyNumRels)	goto NEXT_PRES;						
				if(Freely_Reduce() > 0) goto NEXT_PRES;				
				Length = OrigLength;
				Vertices = 2*NumGenerators;	
				if(Find_Flow_A(NORMAL,0)) goto NEXT_PRES;								
				if(Whitehead_Graph()) goto NEXT_PRES;				
				Depth ++;
				}
			if(DeMerit >= MaxDeMerits) goto NEXT_PRES;
			}
							
NEXT_PRES:	
		ReadPres ++;
		if(ReadPres >= NumFilled) ReadPres = 0;	
		}
}				

int SPM_Compare_Pres_SUR(int k)
{
	/******************************************************************************************
				This routine compares the presentation in SUR[k][] and the
			presentation given by Relators[]. It returns TRUE if they are identical and
			FALSE otherwise.
	******************************************************************************************/
	
	unsigned char 	*p,
					*q;
							
	int 			i;
	
	for(i = 1; i <= NumRelators; i++)
		{
		p = *Relators[i];
		q = *SUR[k][i];
		while(*p && (*p == *q))
			{
			p++;
			q++;
			}
		if(*p || *q) return(FALSE);
		}		
	return(TRUE);			
}

void SPM_SetUpInitialDemerits(void)
{
	unsigned char	*p,
					*q;
					
	int 			Demerit,
					i,
					j,
					MyMinDeMerit;
					
	MyOut = fopen("Heegaard_SPM_Results","a");	
	if(MyOut == NULL)
		{
      	SysBeep(5);
        printf("\nUnable to open the file 'Heegaard_SPM_Results'.");
		printf("\n\nHeegaard will print any new presentation having 'MinDeMerits' only to the terminal window.");
		}
	else	
		printf("\n\nHeegaard will print any new presentation having 'MinDeMerits' to the terminal window and to the file 'Heegaard_SPM_Results'.");					

	if(MyOut != NULL) fprintf(MyOut,"\n\n(C1,C2,C3,C4) = (%d,%d,%d,%d) ",C1,C2,C3,C4);
	
	for(i = 0; i < MAX_SAVED_SPM_PRES; i++) DeMerits[i] = SPM_INFINITE;
	MyMinDeMerit = SPM_INFINITE - 1;
	for(i = 0; i < NumFilled; i++)
		{
		NumGenerators 	= NG[i];
		NumRelators 	= NR[i];
		Vertices 		= 2*NumGenerators;
		for(j = 1; j <= NumRelators; j++)
			{
			if(Relators[j] != NULL) DisposeHandle((char **) Relators[j]);
			Relators[j] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[i][j]));
			if(Relators[j] == NULL) Mem_Error();
			p = *Relators[j];
			q = *SUR[i][j];
			while( (*p++ = *q++) ) ;	
			}			
		Demerit = SPM_ComputeDeMerits(TRUE);
		if(Demerit == -1) 
			DeMerits[i] = SPM_INFINITE;			
		else 
			DeMerits[i] = Demerit;
		if(DeMerits[i] <= MyMinDeMerit)
			{
			MyMinDeMerit = DeMerits[i];
			printf("\n\nLength %lu, InitialMinDeMerits %d, ",SURL[i],MyMinDeMerit);
        	printf("( %lu, %d, %d, %d ) ",Delta,NumPrim1,NumPrim2,NumPairsSepVerts2);
			for(j = 1; j <= NR[i]; j++) printf("\n    %s ",*SUR[i][j]);
			if(MyOut != NULL)
				{
				fprintf(MyOut,"\n\nLength %lu, InitialMinDeMerits %d, ",SURL[i],MyMinDeMerit);
        		fprintf(MyOut,"( %lu, %d, %d, %d ) ",Delta,NumPrim1,NumPrim2,NumPairsSepVerts2);
				for(j = 1; j <= NR[i]; j++) fprintf(MyOut,"\n    %s ",*SUR[i][j]);				
				}
			}		
		}
}

int SPM_LocateMaxDeMerits(void)
{
	int 	i;
	
	for(i = 0, MaxDeMerits = 0; i < MAX_SAVED_SPM_PRES; i++)
		{
		if(DeMerits[i] > MaxDeMerits)
			{
			MaxDeMerits = DeMerits[i];
			MaxDeMeritsLoc = i;
			}
		if(DeMerits[i] < MinDeMerits) 
			{
			MinDeMerits = DeMerits[i];
			MinDeMeritsLoc = i;
			}
		}
		
	if(MaxDeMerits == 0) return(-1);
return(0);			
}

int SPM_ComputeDeMerits(char F1)
{	
	unsigned char 	*p,
					*q;
	
	int				DeMerit,
					i;
					
	unsigned long	SSLength,
					SSSLength;
														
	if(F1)
		{		
		for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
			Length -= NumRelators;
		Fill_A(NumRelators);
		if(Whitehead_Graph()) return(-1);
		}
	
	SSLength = Length;
	
	for(i = 1; i <= NumRelators; i++)
		{
		if(SaveRelators[i] != NULL) DisposeHandle((char **) SaveRelators[i]);
		SaveRelators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
		if(SaveRelators[i] == NULL) Mem_Error();					
		p = *SaveRelators[i];
		q = *Relators[i];
		while( (*p++ = *q++)) ;		
		}		
		
	for(i = 1; i <= NumRelators; i++)
		{
		if(SaveDualRelators[i] != NULL) DisposeHandle((char **) SaveDualRelators[i]);
		SaveDualRelators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) DualRelators[i]));
		if(SaveRelators[i] == NULL) Mem_Error();					
		p = *SaveDualRelators[i];
		q = *DualRelators[i];
		while( (*p++ = *q++)) ;		
		}
	
	if(Freely_Reduce() > 0) return(-1);
	Length = OrigLength;
	Fill_A(NumRelators);
	Get_Matrix();				
	NumPrim1 = SPM_Count_Primitives();						
	for(i = 1; i <= NumRelators; i++)
		{
		if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
		Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SaveDualRelators[i]));
		if(Relators[i] == NULL) Mem_Error();					
		p = *Relators[i];
		q = *SaveDualRelators[i];
		while( (*p++ = *q++)) ;		
		}
	MyNumGens = NumGenerators;
	MyNumRels = NumRelators;
	Vertices  = 2*NumGenerators;
	Rewrite_Input();
	if(NumGenerators < MyNumGens) return(-1);	
	if(NumRelators < MyNumRels)	return(-1);						
	if(Freely_Reduce() > 0) return(-1);		/* A dual relator reduced to the empty word. */
	Length = OrigLength;		
	if(Find_Flow_A(NORMAL,0)) return(-1);	
	SSSLength = Length;
	NumPrim2 = SPM_Count_Primitives();
	Fill_A(NumRelators);
	Get_Matrix();
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;	
	if(Connected_(0,0) == FALSE) 
		NumPairsSepVerts2 = Vertices;
	else
		{
		NumPairsSepVerts2 = 0;
		if(SPM_Sep_Pairs(0,0,1)) NumPairsSepVerts2 = 1;	
		}
	Delta = SSLength - SSSLength;		
	DeMerit = C1*Delta + C2*NumPrim1 + C3*NumPrim2 + C4*NumPairsSepVerts2;			
	return(DeMerit);
}	

int SPM_Count_Primitives(void)
{		
	/******************************************************************************************
		This routine takes each relator in turn and calls Check_Primitivity() to determine if
		that relator is a primitive. It returns the number of relators which are primitives.
	******************************************************************************************/
	
	unsigned char 	*p,
					*q,
					*r;
							
	int 			i,
					SaveNumGenerators;	
							
	unsigned int 	j;
						 		
	if(NumGenerators == 1) return(0);
	SaveNumGenerators = NumGenerators;
	Vertices = 2*NumGenerators;
	
	/******************************************************************************************
	  	Since Relators[1] gets trashed by Find_Primitives() etc., we need to make a copy.
	******************************************************************************************/	
	
	r = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[1]));	
	if(r == NULL) Mem_Error();	
	p = *Relators[1];
	q = r;
	while( (*q++ = *p++) ) ;
	for(i = 1,j = 0; ;)
		{
		if(CheckPrimitivity() == 1) j++;
		NumGenerators = SaveNumGenerators;
		Vertices = 2*NumGenerators;
		if(i >= NumRelators)
			{
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			Relators[1] = (unsigned char **) NewHandle(GetPtrSize((char *) r));
			if(Relators[1] == NULL) Mem_Error();		
			p = *Relators[1];
			q = r;
			while( (*p++ = *q++) ) ;
			DisposePtr((char *)r);		
			return(j);
			}
		i++;
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
		if(Relators[1] == NULL) Mem_Error();		
		p = *Relators[i];
		q = *Relators[1];
		while( (*q++ = *p++) );
		}
	return(0);							
}

int SPM_Sep_Pairs(int VI,int VJ, int FirstCall)
{    
    /******************************************************************************************
        This routine determines whether the graph specified by the adjacency lists in AJ1[],
        has a separating pair of vertices. It deletes, in turn, each vertex, of valence greater
        than two, from the graph and then uses a stack-based version of depth-first-search to
        determine if the resulting graph has a separating vertex. The routine returns TRUE if
        it finds a pair of vertices which "essentially" separates the graph and otherwise
        returns FALSE. If the original graph has more than two major vertices, the routine
        calls Sep_Pairs_Sub() which sets the globals V1 and V2 to the first separating pair of 
        vertices (V1,V2), which follow the ordered pair (VI,VJ) in lexicographic order. 
        Otherwise, it sets the globals V1 and V2 to the ordered pair of major vertices. 
    ******************************************************************************************/
    
    unsigned int   	i,
                	j,
                    k,
                    K,
                    m,
                    *p;
    
    unsigned int    VG[VERTICES],
                    root;
                                  
    if(FirstCall)
    	{
		/**************************************************************************************
			Count the number of vertices of the graph which have valence greater than two,
			and deal with the special case where there are exactly two of these.
		**************************************************************************************/
		
		for(m = MajorVert = 0; m < Vertices; m++)
			if(VWG[m] > 2)
				{
				MajorVert++;
				if(MajorVert == 1)
					i = m;
				else
					{    
					if(MajorVert == 2)
						j = m;
					else
						break;
					}
				} 
				
		if(MajorVert == 2)
			{
			/**********************************************************************************    
				The graph has exactly two major vertices given by the values of i and j.
				If the valence of vertex i is greater than 3 or there is more than one edge 
				joining vertex i and j then the graph does not have a unique planar embedding.
			**********************************************************************************/    
							
			if((VWG[i] > 3) || (A[i][j] > 1))
				{ 
				V1 = i;
				V2 = j;
				NumComps = VWG[i];
				return(TRUE);
				}
			else
				{
				V1 = i;
				V2 = j;
				return(FALSE);                                                    
				}                
			}
        }
        
    /******************************************************************************************
        If we are here, the graph has more than two major vertices, and we go into the main
        loop of the routine.
    ******************************************************************************************/
                            
    for(i = VI; i < Vertices - 1; i ++)
        {
        if(VWG[i] < 3) continue;
      
        for(j = 0; j < Vertices; j++) Number[j] = 0;
        if(i == 0)
            root = 1;
        else
            root = 0;
        Lowpt[i]         = 0;        
        Father[i]        = i;
        NumVert          = 1;
        Number[root]     = 1;
        Lowpt[root]      = 1;
        Father[root]     = root;
        VG[root]         = 0;
        for(p = UpDate,*p = root; p >= UpDate; p--)
            {            
            NEW_VERT:
            m = *p;
            for(k = VG[m]; (j = AJ1[m][k]) < VERTICES; k++)
                {
                if(j == i) continue;
                if(Number[j] == 0)
                    {
                    NumVert       ++;
                    Number[j]     = NumVert;
                    Lowpt[j]      = NumVert;
                    Father[j]     = m;
                    VG[j]         = 0;
                    VG[m]         = k + 1;
                    p             ++;
                    *p            = j;
                    goto         NEW_VERT;        
                    }
                if(j != Father[m] && Number[j] < Lowpt[m])
                    Lowpt[m] = Number[j];        
                }
            if(Lowpt[m] < Lowpt[Father[m]]) Lowpt[Father[m]] = Lowpt[m];    
            }

        if(i == 0 && VJ == 0 && root == 1 && VWG[root] >= 3)
            {
           
            /**********************************************************************************
                Check whether the root of the depth-first-search tree is a cut vertex. This 
                will be the case iff the root has more than one son.
            **********************************************************************************/
        
            for(m = k = 0; (j = AJ1[root][m]) < VERTICES; m++)
                if(Father[j] == root && ++k > 1) break;
            
            if(k > 1 && Sep_Pairs_Sub(i,root)) return(TRUE);
            
            /**********************************************************************************
                If k > 1, the root of the depth-first-search tree is a cut vertex.
                Otherwise, we look for other cut vertices.
            **********************************************************************************/
            
            }

        for(j = 0,K = VERTICES; j < Vertices; j ++)
            {          
            k = Father[j];
            if(VWG[k] < 3) continue;
            if(i == VI && k <= VJ) continue;
            if(i != VI && k <= i) continue;
            if(k >= K) continue;                        
            if(Lowpt[j] >= Number[k] && k != root && Sep_Pairs_Sub(i,k)) K = k;
            }
        if(K < VERTICES) return(TRUE);        
        }    
        
    /******************************************************************************************
        We have checked each pair of distinct major vertices of the graph without finding a
                            pair which produced a proper separation.
    ******************************************************************************************/
                                                        
    return(FALSE);    
}