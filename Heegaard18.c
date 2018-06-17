#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <ctype.h>
#include <string.h>

/*******************************************************************************************
	The routines in this file allow Heegaard to find the canonical representative
	presentation in the orbit of a given presentation and do some identification.
*******************************************************************************************/

/****************************** Functions in Heegaard18.c *****************************************
L 3470 Check_HS_Disjoint_Curves(int NumHSReps,int* HSRepL,char* HSL2)
L 3218 Check_HS_Reducibility(int NumHSReps,int* HSRepL,char* HSL2)
L 2747 Check_HS_Reps(int NumHSReps,int* HSRepL)
L 2077 Check_HS_Simple_Circuits(int NumHSReps,int* HSRepL,char* HSL2)
L 3662 Check_HS_Strong_Irreducibility(int NumHSReps,int* HSRepL,char* HSL2)
L 3759 Check_HS_Strong_IrreducibilityS1(void)
L 4513 Check_HS_Strong_IrreducibilityS2(unsigned char NumPathsInWave,int * PathsInWave,
	   unsigned char ** PP,unsigned char ** PM)
L 1817 Check_HS_Uniqueness(int NumHSReps,int* HSRepL)
L 1892 Check_HS_Uniqueness_Sub1(int MyHSNum,int MyPresNum)
L 3332 Check_HS_Weak_Reducibility(int NumHSReps,int* HSRepL,char* HSL2)
L 2648 CHSP_Check_Simple_Circuits(unsigned int,int*,int,unsigned char**,unsigned char**)
L 1369 Delete_Old_PresentationsSLP(void)
L 1393 Delete_Old_PresentationsSMGP(int MyNumSavedPres,unsigned int* SUR_Num)
L 1761 Display_HS_Diagrams(int NumHSReps,int* HSRepL)
L   65 Find_Canonical_Orbit_Reps(int* MyTable,int MyStart,int MyCompNum,int F1,char RealCompNum)
L 2178 Find_Simple_Circuits(void)
L 2822 Get_Next_Presentation_From_File(char Flag)
L 3581 Get_Relators1_Diagram(void)
L 1555 ID_A_PMQPM(unsigned int i)
L 1490 ID_PMQPM(int MyNumSavedPres,char* PMQPML,unsigned int* SUR_Num)
L 1243 In_File2(int Test,unsigned char ***MyRelators)
L   51 Init_Find_Canonical_Orbit_Reps(int* MyTable,int MyStart,int MyCompNum)
L 2975 Is_IP_In_HS_Reps(int NumHSReps,int* HSRepL)
L 1716 MergeHegSpl(unsigned int i,unsigned int j)
L 1682 Print_Orbit_Reps(int MyNumRelators,int NumOrbits,unsigned int* OrbitNum2SLRNum)
L 1414 qksort2(int first,int last,int NumRelators,unsigned int* SUR_Num)
L 1446 qkst_compare2(int i,int j,int NumRelators,unsigned int* SUR_Num)
L 1481 qkst_swap2(int i,int j)
L 1612 Rewrite_Orbit_Reps(int MyNumRelators,int NumOrbits,unsigned int* OrbitNum2SLRNum)
L 1337 Save_Pres2(void)
L 3055 Search_For_Non_Minimal_UnStabilized_Splittings(char F1,int TargetNumGenerators)
********************************************************************************************/

int     MaxNumPMQPM = 100,
		NumSplittings,
		*Table2 = NULL,
		*Table3 = NULL;

int Init_Find_Canonical_Orbit_Reps(int* MyTable,int MyStart,int MyCompNum)
{
	int		n;
	
	for(n = MyStart; n >= 0; n--)
		{
		ReadPres = MyTable[n];
		if(ComponentNum[ReadPres] > MyCompNum) 	continue;
		if(ComponentNum[ReadPres] == MyCompNum) return(n);
		if(ComponentNum[ReadPres] < MyCompNum) 	return(TOO_LONG);
		}
	return(-1);	
}

int Find_Canonical_Orbit_Reps(int* MyTable,int MyStart,int MyCompNum,int F1,char Try_2_Recognize,char RealCompNum)
{
	char			*HSL2 = NULL,
					*PMQPML = NULL,
					PrintAster = FALSE,
					QuitFlag = FALSE;

	unsigned char	OrbitTooLarge = FALSE,
					*p,
					*q,
					*NewRep = NULL,
					**Temp;				
				
	int				HitSum,
					*HitSumL = NULL,
					*HSRepL  = NULL,				
					LoopSum,
					*LoopSumL = NULL,
					i,
					j,
					k,
					l,
					m,
					MissingPres,
					MissingCanonicalRep,
					MultipleSolns,				
					MyMinNumGenerators,
					MyMinNumRelators,
					MyNumSavedPres,
					*NonSFL = NULL,
					NumHSReps,
					NumOrbits,
					NumSFChecked,
					NumSFFound,
					n,
					NumInOrbit;

	unsigned int	FOHSNum,
					FOLength,
					*HSL = NULL,
					*HSN = NULL,
					*HegSplNumCount = NULL,
					*HegSplNumFirstOrbit = NULL,
					MaxHSNum,
					MyNode,
					MyOrbitSize,
					MyRep,
					*OrbitLength = NULL,
					*OrbitNum2SLRNum = NULL,
					*OrbitSize = NULL,
					SMergers,
					SNumFilled,
					SSNumFilled;
				
	unsigned long	TotalLevelTrans = 0L,
					TotalOrbitSizes = 0L;	
					
	LastPresRead 		= MyStart;			
	MyMinNumGenerators 	= NG[MyTable[MyStart]];
	MyMinNumRelators 	= NR[MyTable[MyStart]];
	MissingPres 		= FALSE;
	MissingCanonicalRep = FALSE;
	SNumFilled 			= NumFilled;
	if(MyMinNumGenerators <= 1)
		{
		printf("\n\nWon't find HS Reps for presentations on fewer than two generators.");
		return(TOO_LONG);
		}
	if(MyMinNumRelators == 0)
		{
		printf("\n\nWon't find HS Reps for empty presentations.");
		return(TOO_LONG);
		}	

	/******************************************************************************************
		Copy the Presentations of the current component on MyMinNumGenerators into SMGP[ ].
	******************************************************************************************/

	for(n = MyStart, MyNumSavedPres = 0; n >= 0; n--)
		{
		if(MyNumSavedPres >= MAX_MIN_GEN_PRES)
			{
			printf("\n\n Find_Canonical_Orbit_Reps has saved %d presentations, which is the current maximal number allowed.",
			MAX_MIN_GEN_PRES);
			printf("\n Will proceed to find Canonical Orbit Representatives of this truncated set of presentations.");
			break;
			}
		ReadPres = MyTable[n];		
		NumGenerators = NG[ReadPres];
		if(NumGenerators > MyMinNumGenerators) 
			{
			LastPresRead = n;
			if(n < MyStart) LastPresRead ++;
			break;
			}
		if(ComponentNum[ReadPres] < MyCompNum) 
			{
			LastPresRead = n;
			if(n < MyStart) LastPresRead ++;
			break;
			}
		NumRelators = NR[ReadPres];
		if(F1 != 2) 
			{
			i = ID_A_PMQPM(ReadPres);
			if(i == FALSE) continue;
			if(i == 2 && MyNumSavedPres > 200) continue;
			}
		if(NumRelators == 0)
			{
			printf("\n\nThe initial presentation was: %s",PresName);
			printf("\n\n Heegaard won't find Canonical Rep Presentations for Free groups!");
			if(Batch && H_Results != NULL) fprintf(H_Results,"\n\n%s	FREE_GROUP",PresName);
			return(TOO_LONG);
			}	
	
		for(i = 1; i <= NumRelators; i++)
			{
			if(SMGP[MyNumSavedPres][i] != NULL) DisposeHandle((char **) SMGP[MyNumSavedPres][i]);
			SMGP[MyNumSavedPres][i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(SMGP[MyNumSavedPres][i] == NULL) Mem_Error();
			q = *SMGP[MyNumSavedPres][i];
			p = *SUR[ReadPres][i];
			while( (*q++ = *p++) ) ;
			}
		
		SUR_Num[MyNumSavedPres] = ReadPres;
		MyNumSavedPres++;
		}
		
	/********************************************************************************** 
		Normally, only the first MaxNumPMQPM presentations on MyMinNumGenerators and 
		MyMinNumRelators in addition to presentations marked PM or QPM are used here. 
	**********************************************************************************/
		
	if(MyNumSavedPres == 0)
		{
		printf("\n\nThe initial presentation was: %s",PresName);
		printf("\n\nNo presentations of C%d meet the requirements of the Canonical Rep routine.",RealCompNum);
		if(Batch && H_Results != NULL) fprintf(H_Results,"	?");
		return(TOO_LONG);
		}
	
	OrbitSize = (unsigned int*) NewPtr((sizeof(int)*(MyNumSavedPres+1)));
	if(OrbitSize == NULL) Mem_Error();
			
	OrbitNum2SLRNum = (unsigned int*) NewPtr((sizeof(int)*(MyNumSavedPres+1)));
	if(OrbitNum2SLRNum == NULL) Mem_Error();
	
	NewRep = (unsigned char*) NewPtr((sizeof(char)*(MyNumSavedPres+1)));
	if(NewRep == NULL) Mem_Error();
		
	PMQPML = (char*) NewPtr((sizeof(char)*(MyNumSavedPres+1)));
	if(PMQPML == NULL) Mem_Error();			

	if(F1 != 2) ID_PMQPM(MyNumSavedPres, PMQPML, SUR_Num);
			
	for(i = 0; i < MyNumSavedPres; i++) 
		{
		OrbitSize[i] = 0;
		NewRep[i] = FALSE;
		BeenChecked[i] = FALSE;
		}

	if(Batch == FALSE)
		{
		printf("\n\n    Computing orbits under level-transformations of %d presentations of component C%d.",MyNumSavedPres,RealCompNum);
		printf("\n    This may take awhile. Hit 's' to get status reports. ");
		printf("\n    Hit 'p' to toggle printing of an * after each orbit is checked.  ");
		printf("\n    Hit ' ' for a chance to skip remaining orbit computations.    \n");
		}
		
	for(NumOrbits = n = 0; n < MyNumSavedPres; n++) if(BeenChecked[n] == FALSE)
		{
		ReadPres 		= SUR_Num[n];
		NumGenerators 	= NG[ReadPres];
		NumRelators 	= NR[ReadPres];
		Vertices 		= 2*NumGenerators;
		Length 			= SURL[ReadPres];
		SLength 		= Length;
		NumOrbits ++;
	
		/********************************************************************
				Set up the root presentation of the orbit under level-
				transformations.
		********************************************************************/
			
		SLP[0] = (unsigned char ***) NewPtr(sizeof(long)*(NumRelators + 1));
		if(SLP[0] == NULL) Mem_Error();
	
		for(i = 1; i <= NumRelators; i++)
			{
			SLP[0][i] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[n][i]));            
			if(SLP[0][i] == NULL) Mem_Error();
			q = *SLP[0][i];	
			p = *SMGP[n][i];
			while( (*q++ = *p++) ) ;                                    
			}
		NumFilled = 0;    
		ReadPres = NumFilled;    
		NumFilled ++;		
		do
			{
			Num_Level_Transformations = 0L;			
			j = Find_Level_Transformations(FALSE,2);
			TotalLevelTrans += Num_Level_Transformations;
			if(j == NOT_CONNECTED)
				{
				printf("\n\nThe Whitehead Graph of Presentation %u is not connected!",SUR_Num[n] + 1);
				printf("\nHeegaard will only find orbits of presentations with connected Whitehead Graphs.");				
				if(OrbitSize) 		DisposePtr((unsigned int*) OrbitSize);
				if(OrbitNum2SLRNum)	DisposePtr((unsigned int*) OrbitNum2SLRNum);
				if(NewRep)			DisposePtr((unsigned char*) NewRep);
				if(PMQPML)			DisposePtr((char*) PMQPML); 
				Delete_Old_PresentationsSLP();
				NumFilled = SNumFilled;
				if(Batch && H_Results != NULL) fprintf(H_Results,"\n\n%s	NOT_CONNECTED",PresName);
				return(TOO_LONG);
				}
			if(j == FULL_HOUSE)
				{
				printf("\nThe orbit of Presentation %5u Length %5lu contains at least %u members.",
				SUR_Num[n] + 1, SURL[SUR_Num[n]], MAX_SAVED_PRES - 3);
				if(Batch && H_Results != NULL) fprintf(H_Results,"\n%s	ORBIT_TOO_LARGE",PresName);
				OrbitTooLarge = TRUE;
				goto NEXT_PRES;
				}
			if(j == 5)
				{
				printf("\n\nWe have run out of memory set aside for orbits under level-presentations!!!!");
				Compute_Stabilizers = FALSE;
				if(OrbitSize)		DisposePtr((unsigned int*) OrbitSize);
				if(OrbitNum2SLRNum)	DisposePtr((unsigned int*) OrbitNum2SLRNum);
				if(NewRep)			DisposePtr((unsigned char*) NewRep);
				if(PMQPML)			DisposePtr((char*) PMQPML);
				Delete_Old_PresentationsSLP();
				NumFilled = SNumFilled;
				if(Batch && H_Results != NULL) fprintf(H_Results,"\n\n%s	ORBIT_TOO_LARGE",PresName);
				return(TOO_LONG);
				}
			if(j == TOO_LONG) 
				{
				printf("\n\nNumFilled = %u, Find_Level_Transformations() returned TOO_LONG.", NumFilled);
				if(OrbitSize)		DisposePtr((unsigned int*) OrbitSize);
				if(OrbitNum2SLRNum)	DisposePtr((unsigned int*) OrbitNum2SLRNum);
				if(NewRep)			DisposePtr((unsigned char*) NewRep);
				if(PMQPML)			DisposePtr((char*) PMQPML);
				Delete_Old_PresentationsSLP();
				NumFilled = SNumFilled;
				if(Batch && H_Results != NULL) fprintf(H_Results,"\n\n%s	TOO_LONG_ERROR",PresName);
				return(TOO_LONG);
				}  
			ReadPres ++;
			}
		while(ReadPres < NumFilled);

NEXT_PRES:
		
    	OrbitSize[n] = NumFilled;
    	TotalOrbitSizes += NumFilled;
	
		/*****************************************************************
			Find the node of the canonical representative in the orbit.
		*****************************************************************/	
	
		for(MyNode = 0; Left[MyNode] < INFINITE; MyNode = Left[MyNode]) ;
	
		BeenChecked[n] = NumOrbits + MAX_MIN_GEN_PRES;
	
		/******************************************************************
			Check if any current unchecked presentations in SMGP[] lie in 
			the orbit of SMGP[n]. 
		******************************************************************/
	
		for(i = 0; i < MyNumSavedPres; i++)
			{
			ReadPres = SUR_Num[i];
			if((BeenChecked[i] == FALSE) && (NR[ReadPres] == NumRelators) && (SURL[ReadPres] == SLength)) 
			if(In_File2(TRUE, SMGP[i]) < INFINITE) BeenChecked[i] = NumOrbits;
			}
		
		/*******************************************************************
			If MyNode > 0, swap presentation SMGP[n] with SLP[MyNode].
							Set NewRep[n] = TRUE.
		*******************************************************************/
	
		if(MyNode)
			{
			for(i = 1; i <= NumRelators; i++)
				{
				Temp 			= SMGP[n][i];
				SMGP[n][i] 		= SLP[MyNode][i];
				SLP[MyNode][i] 	= Temp;
				}
			NewRep[n] = TRUE;
			MissingCanonicalRep = TRUE;
			}
	
		Delete_Old_PresentationsSLP();
		
		switch(mykbhit())
			{
			case ' ':			
				printf("\n	Status: In 'Find_Canonical_Orbit_Reps()'. Processed %d of %d presentations, Sum of Orbit Sizes %lu, Now checking presentations of Length >= %lu, Total Level Transformations %lu    ",
					n,MyNumSavedPres,TotalOrbitSizes,SURL[SUR_Num[n]],TotalLevelTrans); 
				printf("\n  Hit 'c' to continue. Hit 'q' to skip remaining orbit computations. Hit 'Q' to quit.   ");
				fflush(stdout);			
				GET_RESPONSE2:			
				switch(WaitkbHit())
					{
					case 'c':
						break;
					case 'q':
						goto REPORT_RESULTS;
					case 'Q':
						QuitFlag = TRUE;
						goto END;		
					default: goto GET_RESPONSE2;
					}
				break;
			case 'p':
				if(PrintAster) PrintAster = FALSE;
				else PrintAster = TRUE;							
			case 's':			
				printf("\n	Status: In 'Find_Canonical_Orbit_Reps()'. Processed %d of %d presentations. Sum of Orbit Sizes %lu, Now checking presentations of Length >= %lu, Total Level Transformations %lu    ",
					n,MyNumSavedPres,TotalOrbitSizes,SURL[SUR_Num[n]],TotalLevelTrans);
				fflush(stdout);							 
				break;
			default:
				break;
			}
		if(!Batch && PrintAster) printf("*");									
		}		

	/*******************************************************************
							Report Results.
	*******************************************************************/
	
REPORT_RESULTS:	

	if(Batch == FALSE && !Check_for_1_HS)
		{	
		if(MyNumSavedPres == 1)
			{
			if(TotalComp == 1)  printf("\n\n Heegaard found one Presentation on %d Generators:",MyMinNumGenerators);
			else printf("\n\n Heegaard found one Presentation of Component %d on %d Generators:",
				MyCompNum, MyMinNumGenerators);
			if(F1 != 2)
			printf("\n Note xx' indicates Presentation xx is pseudo-minimal or quasi-pseudo-minimal.\n\n");
			}
		else
			{
			if(TotalComp == 1) printf("\n\n Heegaard found the following %d Presentations on %d Generators:",
				MyNumSavedPres,MyMinNumGenerators);
			else printf("\n\n Heegaard found the following %d Presentations of Component %d on %d Generators:",
				MyNumSavedPres, MyCompNum, MyMinNumGenerators);
			if(F1 != 2)
			printf("\n Note xx' indicates Presentation xx is pseudo-minimal or quasi-pseudo-minimal.\n\n");
			}
		printf("{");
		for(i = 0; i < MyNumSavedPres - 1; i++) 
			{
			if(F1 != 2 && PMQPML[i])
				printf("%d',",SUR_Num[i] + 1);
			else		
				printf("%d,",SUR_Num[i] + 1);
			}
		if(F1 != 2 && PMQPML[i])
			printf("%d'}",SUR_Num[i] + 1);
		else		
			printf("%d}",SUR_Num[i] + 1); 
		}
	
	if(Table2 != NULL) DisposePtr((int*) Table2);	
	Table2 = (int*) NewPtr((sizeof(int)*NumOrbits));
	if(Table2 == NULL) Mem_Error();
	if(Table3 != NULL) DisposePtr((int*) Table3);
	Table3 = (int*) NewPtr((sizeof(int)*(NumOrbits + 1)));
	if(Table3 == NULL) Mem_Error();
	HitSumL = (int*) NewPtr((sizeof(int)*NumOrbits));
	if(HitSumL == NULL) Mem_Error();
	LoopSumL = (int*) NewPtr((sizeof(int)*NumOrbits));
	if(LoopSumL == NULL) Mem_Error();	

	for(i = j = 0; i < MyNumSavedPres; i++) if(BeenChecked[i] > MAX_MIN_GEN_PRES)
		{
		Table2[j] = BeenChecked[i] - MAX_MIN_GEN_PRES;
		Table3[Table2[j]] = i;
		j++;
		}
	 	
	qksort2(0, NumOrbits, MyMinNumRelators, SUR_Num);

	if(Batch == FALSE && !Check_for_1_HS)
		{
		if(NumOrbits == 1)
			printf("\n\n These all belong to one orbit.");
		else	 
			printf("\n\n These fall into the following %d orbits under level-transformations:\n",NumOrbits);
		}
		
	HSN 					= (unsigned int*) NewPtr((sizeof(int)*NumOrbits));
	if(HSN 					== NULL) Mem_Error();
	HegSplNumCount 			= (unsigned int*) NewPtr((sizeof(int)*SNumFilled));
	if(HegSplNumCount 		== NULL) Mem_Error();	
	HegSplNumFirstOrbit 	= (unsigned int*) NewPtr((sizeof(int)*SNumFilled));
	if(HegSplNumFirstOrbit 	== NULL) Mem_Error();
	OrbitLength 			= (unsigned int*) NewPtr((sizeof(int)*NumOrbits));
	if(OrbitLength 			== NULL) Mem_Error();	
	for(i = 0; i < SNumFilled; i++) HegSplNumCount[i] = 0;
	SMergers = Mergers;
	
	for(k = NumOrbits - 1; k >= 0; k--)
		{
		j = Table2[k];
		for(i = 0; i < MyNumSavedPres; i++) if(BeenChecked[i] == j + MAX_MIN_GEN_PRES)
			{
			MyOrbitSize = OrbitSize[i];
			OrbitLength[k] = SURL[SUR_Num[i]];
			break;
			}	
		for(i = NumInOrbit = 0; i < MyNumSavedPres; i++) 
			if((BeenChecked[i] == j) || (BeenChecked[i] == j + MAX_MIN_GEN_PRES)) NumInOrbit++;
		if(MyOrbitSize > NumInOrbit) MissingPres = TRUE;	
		for(i = HitSum = LoopSum = 0; i < MyNumSavedPres; i++) if((BeenChecked[i] == j) || (BeenChecked[i] == j + MAX_MIN_GEN_PRES)) 
			{
			HitSum  += SURNumX[SUR_Num[i]];
			LoopSum += NumLoops[SUR_Num[i]];
			}
		HitSumL[k]  = HitSum;
		LoopSumL[k] = LoopSum;		

		for(i = 0; i < MyNumSavedPres; i++) if((BeenChecked[i] == j) || (BeenChecked[i] == j + MAX_MIN_GEN_PRES))
			{
			l = i;
			break;
			}
		for(i = l + 1; i < MyNumSavedPres; i++) if((BeenChecked[i] == j) || (BeenChecked[i] == j + MAX_MIN_GEN_PRES))
			{
			MergeHegSpl(SUR_Num[l],SUR_Num[i]);
			l = i;
			}
		HSN[k] = HegSplNum[SUR_Num[l]];
		HegSplNumCount[HSN[k]] ++; 		/** Counts the number of orbits with the same HSN. **/
		HegSplNumFirstOrbit[HSN[k]] = k;

		if(Batch == FALSE && !Check_for_1_HS) 
		printf("\nOrbit %4d, Size %6u, Length %6u, OrbHits %6d, OrbLoops %6d, HegSplNum %u, {",
		k + 1, MyOrbitSize, OrbitLength[k],HitSum,LoopSum,HSN[k]);
		
		for(i = 0; i < MyNumSavedPres; i++) if((BeenChecked[i] == j) || (BeenChecked[i] == j + MAX_MIN_GEN_PRES)) 
			{
			NumInOrbit--;
			if(Batch == FALSE && !Check_for_1_HS)
				{
				if(NumInOrbit)
					{
					if(F1 != 2 && PMQPML[i])
						printf("%d',",SUR_Num[i] + 1);
					else		
						printf("%d,",SUR_Num[i] + 1);
					}
				else
					{
					if(F1 != 2 && PMQPML[i])
						printf("%d'}",SUR_Num[i] + 1);
					else		
						printf("%d}",SUR_Num[i] + 1); 
					}
				}		
			}
		}
	if(Batch == FALSE && !Check_for_1_HS) printf("\n");
		
	for(k = NumOrbits - 1; k >= 0; k--)
		{
		if(NumOrbits == 1)
			j = BeenChecked[0] - MAX_MIN_GEN_PRES;
		else
			j = Table2[k]; 
		for(i = 0; i < MyNumSavedPres; i++) if(BeenChecked[i] == j + MAX_MIN_GEN_PRES)
			{
			ReadPres 		= SUR_Num[i];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			MyOrbitSize     = OrbitSize[i];
			if(NewRep[i]) 
				MyRep = INFINITE;
			else 
				MyRep = ReadPres + 1;
			if(Batch == FALSE && !Check_for_1_HS)
				{
				if(NumRelators == 1)
					{
					if(MyRep == INFINITE)
						printf("\nOrbit %d: Size %u, Canonical Rep Pres ??, Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
						k + 1, MyOrbitSize, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
					else
						{
						if(F1 != 2 && PMQPML[i])
							printf("\nOrbit %d: Size %u, Canonical Rep Pres %u', Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
							k + 1, MyOrbitSize, MyRep, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
						else	
							printf("\nOrbit %d: Size %u, Canonical Rep Pres %u, Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
							k + 1, MyOrbitSize, MyRep, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
						}
					}
				else
					{
					if(MyRep == INFINITE)
						printf("\nOrbit %d: Size %u, Canonical Rep Pres ??, Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
						k + 1, MyOrbitSize, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
					else
						{
						if(F1 != 2 && PMQPML[i])
							printf("\nOrbit %d: Size %u, Canonical Rep Pres %u', Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
							k + 1, MyOrbitSize, MyRep, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
						else	
							printf("\nOrbit %d: Size %u, Canonical Rep Pres %u, Gen %d, Rel %d, Length %lu, OrbHits %d, HegSplNum %u",
							k + 1, MyOrbitSize, MyRep, NumGenerators, NumRelators, Length, HitSumL[k],HSN[k]);
						}
					}
				}	
			OrbitNum2SLRNum[k+1] = i;	
			if(Batch == FALSE && !Check_for_1_HS) Print_Relators(SMGP[i], NumRelators);
			}
		}

	/* Count the number of Heegaard Splittings. */

	for(i = NumSplittings = 0; i < SNumFilled; i++) if(HegSplNumCount[i]) NumSplittings ++;
	HSL = (unsigned int*) NewPtr((sizeof(int)*(NumSplittings + 1)));
	if(HSL == NULL) Mem_Error();
	for(i = NumSplittings = 0; i < SNumFilled; i++) if(HegSplNumCount[i]) 
		HSL[NumSplittings++] = HegSplNumFirstOrbit[i];
	HSRepL = (int*) NewPtr((sizeof(int)*(NumOrbits + NumSplittings)));
	if(HSRepL == NULL) Mem_Error();
	
	/* Sort the Heegaard Splittings by FirstOrbitNumbers. */
		
	m = 1;
	do
		{
		for(i = j = 0; i < NumSplittings - m; i++) if(HSL[i] > HSL[i+1])
			{
			k = HSL[i];
			HSL[i] = HSL[i+1];
			HSL[i+1] = k;
			j++;
			}
		m++;	
		}		
	while(j);		

	/* For each Heegaard splitting, print the orbit reps of that splitting with minimal length. */
	
	if(Batch == FALSE && F1 == 1)
		{	
		printf("\n******* Below are the minimal genus Heegaard splittings and the minimal length *******");
		printf("\n******* orbit representatives which Heegaard found for each splitting.         *******\n");
		}		
	for(i = NumHSReps = n = 0; i < NumSplittings; i++)
		{
		FOLength = OrbitLength[HSL[i]];
		FOHSNum  = HSN[HSL[i]];
		for(k = m = 0; k < NumOrbits; k++) if(OrbitLength[k] == FOLength && HSN[k] == FOHSNum)
			{
			if(NumOrbits == 1)
				j = BeenChecked[0] - MAX_MIN_GEN_PRES;
			else
				j = Table2[k]; 
			for(l = 0; l < MyNumSavedPres; l++) if(BeenChecked[l] == j + MAX_MIN_GEN_PRES)
				{
				ReadPres 		= SUR_Num[l];
				NumGenerators 	= NG[ReadPres];
				NumRelators 	= NR[ReadPres];
				Length 			= SURL[ReadPres];
				m++;
				if(m == 1) HSRepL[NumHSReps ++] = -(i+1);
				if(NewRep[l]) HSRepL[NumHSReps ++] = l + INFINITE;
				else HSRepL[NumHSReps ++] = ReadPres;				
				if(F1 == 1 && !B10B11Recognized) 
					{
					if(Batch) printf("\n");
					printf("\n%.25s . . . C%d) HS %u, P %d, L %lu, Gen %d, Rel %d ",PresName,RealCompNum,i+1,m,Length,NumGenerators,NumRelators);	
					Print_Relators(SMGP[l],NumRelators);
					}	
				if((Batch == 10 || Batch == 11) && H_Results != NULL && B10B11HSReps == TRUE && F1 == 1)
					{
					if(B10B11SaveOnlyHS1P1 == 1)
						{
						fprintf(H_Results,"\n\n%.25s . . . C%d) HS %u, P %d, L %lu, Gen %d, Rel %d ",PresName,RealCompNum,i+1,m,Length,NumGenerators,NumRelators);					
						Print_Relators2(SMGP[l],NumRelators);
						}
					if(B10B11SaveOnlyHS1P1 == 2 && i == 0 && m == 1)
						{
						fprintf(H_Results,"\n\n%.25s . . . C%d) HS %u, P %d, L %lu, Gen %d, Rel %d ",PresName,RealCompNum,i+1,m,Length,NumGenerators,NumRelators);
						Print_Relators2(SMGP[l],NumRelators);
						}
					if(B10B11SaveOnlyHS1P1 == 3 && NumGenerators == 2 && NumRelators == 1)				
						{
						if(++n == 1) fprintf(H_Results,"\n\n%.25s . . . C%d)",PresName,RealCompNum);
						fprintf(H_Results,"\nL %lu %.25s",Length,*SMGP[l][1]);	
						}												
					if(B10B11SaveOnlyHS1P1 == 4 && NumSplittings == 1 && NumGenerators == 2 && NumRelators == 1)				
						{
						fprintf(H_Results,"\n\n%.25s . . . C%d)",PresName,RealCompNum);
						fprintf(H_Results,"\nL %lu %.25s",Length,*SMGP[l][1]);
						}
					}								
				}		
			}
		}
	if(Batch == FALSE || Batch == 53)
		{
		if(Batch == FALSE && F1 == 1)
			{
			printf("\n******* Above are the minimal genus Heegaard splittings and the minimal length *******");
			printf("\n******* orbit representatives which Heegaard found for each splitting.         *******\n\n");	
			}
		if(Batch == 53 && F1 == 1) printf("\n\n");	
		if(F1 == 1) printf("(  HS,  HSNum, FirstOrbit, Length, Orbits, FirstOrbitHits, Total HS Hits, Total HS Loops)\n");
		for(l = 0; l < NumSplittings; l++)
		for(i = 0; i < SNumFilled; i++) if(HegSplNumCount[i] && HegSplNumFirstOrbit[i] == HSL[l]) 
			{
			if(F1 == 1) printf("(%4u, %6d, %10u, %6u, %6u, %14d,",l+1,i,HSL[l]+1,OrbitLength[HSL[l]],HegSplNumCount[i],HitSumL[HSL[l]]);
			for(k = j = m = 0; k < NumOrbits; k++) if(HSN[k] == i) 
				{
				j += HitSumL[k];
				m += LoopSumL[k];
				}
			if(F1 == 1) printf(" %13d, %14d)\n",j,m);	
			}
		if(Batch == FALSE && !Check_for_1_HS)
			{	
			if(F1 == 1) printf("\n******* The table above gives more detailed info about the splittings Heegaard found. *******\n");
			SSNumFilled = SNumFilled;
			if(PRIM[SNumFilled - 1] == 70 || PRIM[SNumFilled - 1] == 170) SSNumFilled --;
			if(SSNumFilled == 0) SSNumFilled = 1;
			if(BreadthFirstSearch && F1 == 1)
				{
				printf("\n Checking this list of candidate HS Reps by copying and pasting it into \042Heegaard_Input_Presentations\042\n");
				printf(" and rerunning individual presentations may reveal that \042Splittings\042 with relatively few hits\n");
				printf(" or HSNum > %u merge with others. In addition, further processing may reveal new or additional\n",FR[SSNumFilled - 1] + 1);
				printf(" minimal length representative presentations for a splitting.");
				}
			if(!BreadthFirstSearch && F1 == 1)
				{
				printf("\n Checking this list of candidate HS Reps by copying and pasting it into \042Heegaard_Input_Presentations\042\n");
				printf(" and rerunning individual presentations may reveal that \042Splittings\042 with relatively few hits\n");		
				printf(" merge with others. In addition, further processing may reveal new or additional minimal\n");
				printf(" length representative presentations for a splitting.");
				}
			}
		}

 	if(Check_for_1_HS && NumSplittings > 1 && Check_HS_Reducibility(NumHSReps,HSRepL,HSL2) == 1) printf("\nEach HS is reducible!");	
		
	if(Check_for_1_HS) goto END;
		
	if((B10B11HSReps || Batch == 53) && TotalComp == 1) /* If B10B11HSReps or Batch == 53, find and print the largest HSNum that appears. */
		{
		for(i = 0,MaxHSNum = 0; i < NumOrbits; i++) 
		if(HSN[i] > MaxHSNum) MaxHSNum = HSN[i];
		printf("\n\nMaxHSNum %u, Limit %u. MaxHSNum << Limit suggests Heegaard found all/most HS Reps.",MaxHSNum,MyMaxSavedPres);
		}
				
	if(OrbitTooLarge) printf("\n\nAn orbit was too large. Hence the orbit's Rep can't be guaranteed. Scroll back for details.");
				
	if(Batch == FALSE && F1 == 1) Check_HS_Uniqueness(NumHSReps,HSRepL);
		
	if(Batch == FALSE && MyCompNum == 1) printf("\n\nThe initial presentation was: %s",PresName);

	if(Batch == FALSE && MyCompNum > 1)
	printf("\n\nThe initial presentation was: Pres %d of Summand %d of %s",MyStart+1,MyCompNum,PresName);

	if(Batch == FALSE)
		{			
		if(NumOrbits == 1)
			{
			if(MyNumSavedPres > 1)
				{
				printf("\n\nNote %d presentations on %d generators form one orbit under level-transformations.\n",
				MyNumSavedPres, MyMinNumGenerators);
				printf("These all lie on one Heegaard surface.");
				}
			}
		else
			{
			printf("\n\nNote %d presentations on %d generators form %d orbits under level-transformations.\n",
			MyNumSavedPres, MyMinNumGenerators, NumOrbits);
			if(NumSplittings == 1)
				printf("These all lie on one Heegaard surface.");
			else
				{
				if(F1 == 1)
					printf("These form %u equivalence classes under bandsums; so may represent %u Heegaard splittings."
					,NumSplittings, NumSplittings);
				if(F1 == 2)
					printf("These form %u equivalence classes under level-transformations; so may represent %u Heegaard splittings."
					,NumOrbits, NumOrbits);
				}
			}	
	
		i = Mergers - SMergers;	
		if(i == 1 && F1 == 1)
			printf("\n\n One additional merger was performed.");			
		if(i > 1 && F1 == 1)
			printf("\n\n %d additional mergers were performed.",i);	
			
		if(MyNumSavedPres >= MAX_MIN_GEN_PRES)
			printf("\n\n Note Heegaard only partitioned the first %d presentations into orbits.",MyNumSavedPres);
		
		if(F1 == 1)
			printf("\n\n Note xx' indicates Presentation xx is pseudo-minimal or quasi-pseudo-minimal.");	
		if(MissingPres)
			{
			printf("\n\n Note: Initially Heegaard does not look for every presentation in an orbit under");
			printf("\n level-transformations. Hence an orbit may contain presentations not listed.");
			}
		if(MissingCanonicalRep)
			printf("\n In particular, the Canonical Rep Presentation may be missing from an orbit list.");

		if(F1 == 2)
			{
			printf("\n\n Note: The routine Just_Delete_Primitives() just deletes primitives from the initial presentation,");
			printf("\n does not check realizability, and does no bandsums. If the initial presentation is not realizable,");
			printf("\n none of Heegaard's behavior and results beyond this point are guaranteed. However, if the initial");
			printf("\n presentation is realizable, all should be well. \n HOWEVER, NO BANDSUMS IMPLIES NO MEANINGFUL HS REPS!");
			printf("\n\n HIT 'p' TO PROCEED ANYWAY. HIT ANY OTHER KEY TO ABORT.    ");

			if(Batch == FALSE)
				{
				switch(WaitkbHit())
					{
					case 'p':
						F1 = 3;
						break;
					default:
						break;        
					}
				}		
			}
		}		

	if(Try_2_Recognize)
		{	
		FoundFiniteSF = FoundSF = FoundBigSF = FoundEssentialTorus = NumSFFound = 0;
		if(HSL2) DisposePtr((char*) HSL2);
		HSL2 = (char *) NewPtr((sizeof(char)*(NumSplittings + 1)));
		if(HSL2 == NULL) Mem_Error();
		for(i = 1; i <= NumSplittings; i++) HSL2[i] = FALSE;
		
		/************************************************************************************
			If this manifold is closed and has genus greater than two, check whether any 
			of the Heegaard splitting Orbit Reps are vertical splittings of Seifert fibered
			spaces over orientable base spaces. 
		*************************************************************************************/
			
		if((MyMinNumGenerators > 2 && MyMinNumRelators == MyMinNumGenerators) && 
			(Batch == FALSE || ((Batch == 10 || Batch == 11) && B10B11Recognized == TRUE)))		
			{
			for(i = 1,j = 0; CBC[1][i] < BDRY_UNKNOWN; i++) j += CBC[1][i];
			if(j == 0) /* The manifold is closed. */
				{				
				NumGenerators = MyMinNumGenerators;
				NumRelators = MyMinNumRelators;
				HSL[NumSplittings] = NumOrbits;
				for(l = 0; l < NumSplittings; l++)
					{
					for(k = HSL[l] + 1,j = HSN[k - 1]; (k <= NumOrbits) && (k < HSL[l+1] + 1); k++)
						{	
						if(HSN[k - 1] != j) continue;				
						if(OrbitLength[k - 1] > OrbitLength[HSL[l]]) break;						
						m = OrbitNum2SLRNum[k];					
						for(i = 1; i <= NumRelators; i++)
							{						
							if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
							Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[m][i]));
							if(Relators[i] == NULL) Mem_Error();		
							p = *SMGP[m][i];
							q = *Relators[i];
							while((*q++ = *p++)) ;						
							}
						Check_for_Big_SF(l,k,OrbitLength[k-1]);
						if(FoundBigSF) break;
						}
					if(FoundBigSF) break;
					}
				}
			}
			
		if(B10B11Recognized && FoundBigSF) goto END;			
		
		if((Batch == 10 || Batch == 11) && !B10B11Recognized) goto END;
			
		if(F1 != 2)
			{
			/****** Check which genus two presentations are Seifert Fibered. And locate meridian reps. ******/
	
			NonSFL = (int*) NewPtr((sizeof(int)*NumOrbits));
			if(NonSFL == NULL) Mem_Error();

			MultipleSolns = 0;	

			for(k = 0, NumSFChecked = NumSFFound = 0; k < NumOrbits ; k++)
				{
				if(NumOrbits == 1)
					j = BeenChecked[0] - MAX_MIN_GEN_PRES;
				else
					j = Table2[k]; 
				for(i = 0; i < MyNumSavedPres; i++) if(BeenChecked[i] == j + MAX_MIN_GEN_PRES)
					{
					ReadPres 		= SUR_Num[i];
					NumGenerators 	= NG[ReadPres];
					NumRelators 	= NR[ReadPres];
					Vertices		= 2*NumGenerators;
					Length 			= SURL[ReadPres];
					MyOrbitSize     = OrbitSize[i];
					if(NumGenerators > 2) continue;
					if(NumRelators > 2) continue;
					if(NewRep[i] || PMQPML[i] || (k == 0) || F1 == 3)
						{
						if(!B10B11Recognized && NumGenerators == 2 && NumRelators == 1)
							{
							if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
							Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[i][1]));
							if(Relators[1] == NULL) Mem_Error();
							p = *Relators[1];
							q = *SMGP[i][1];
							while( (*p++ = *q++) ) ;
							Length = GetHandleSize((char **) Relators[1]) - 1;
							Genus_Two_Meridian_Reps(k+1,0);
							}					
					   for(l = 1, Length = 0; l <= NumRelators; l++)
							{
							if(Relators[l] != NULL) DisposeHandle((char **) Relators[l]);
							Relators[l] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[i][l]));
							if(Relators[l] == NULL) Mem_Error();
							p = *Relators[l];
							q = *SMGP[i][l];
							while( (*p++ = *q++) ) ;
							Length += GetHandleSize((char **) Relators[l]) - 1;
							}					
						NumSFChecked ++;
						SFSolV[1] = ReadPres;
						SFSolV[2] = MyCompNum;
						SFSolV[3] = NumRelators;
						if(B10B11Recognized)
							m = Genus_Two_Seifert_Fibered(k + 1,0);
						else
							m = Genus_Two_Seifert_Fibered(k + 1,1);
						if(m == 13 || m == 14)
							NumSFFound ++;
						else 
							NonSFL[NumSFChecked - NumSFFound - 1] = k + 1;
						if(m == 14) MultipleSolns ++;	
						if(NumSFFound > MultipleSolns) goto FOUND_GOOD_SOLN;
						}
					}
				}	
			}

	FOUND_GOOD_SOLN:

		if(B10B11Recognized && (FoundFiniteSF || FoundSF))
			{
			if(SFSols[MyCompNum]) DisposePtr((int*) SFSols[MyCompNum]);
			SFSols[MyCompNum] = (int*) NewPtr(sizeof(int)*20);
			if(SFSols[MyCompNum] == NULL) Mem_Error();
			for(i = 0; i < 20; i++) SFSols[MyCompNum][i] = SFSolV[i];
			Print_SFComp(MyCompNum);
			goto END;
			}
	
		if(F1 != 2 && !B10B11Recognized)
			{
			if(NumSFFound == 1)
				{
				if(NumSFChecked == 1)
					printf("\n\n Heegaard checked one orbit rep presentation, which was SF.");			
				else	
					printf("\n\n Heegaard found one SF presentation in the %d orbit rep presentations checked.",NumSFChecked);
				}
			if(NumSFFound > 1)
				{
				printf("\n\n Heegaard found %d SF presentations in the %d orbit rep presentations checked.",NumSFFound,NumSFChecked);
				}		
			if(NumSFChecked > NumSFFound)
				{
				printf("\n\n Orbits of rep presentations checked but not recognized as SF: {");
				for(i = 0; i < NumSFChecked - NumSFFound -1; i++) printf("%d,",NonSFL[i]);
				printf("%d}",NonSFL[i]);
				}
			if(MultipleSolns && NumSFFound == MultipleSolns)
				{
				printf("\n\n		A Potential Seifert Fibration Ambiguity Exists!");
				printf("\n These ambiguities arise in the following way: Suppose M = ±SF(0;e;B1/A1,B2/A2,B3/A3).");
				printf("\n Then, given A1,A2,A3,B1, and B2, which Heegaard computes, there must exist integers"); 
				printf("\n B3 and e with gcd(A3,B3) = 1 such that:");
				printf("\n 	 |H1(M)| = B1*A2*A3 + A1*B2*A3 + A1*A2*B3 - e*A1*A2*A3, or");
				printf("\n 	-|H1(M)| = B1*A2*A3 + A1*B2*A3 + A1*A2*B3 - e*A1*A2*A3.");
				printf("\n Generally, only one of these equations holds. However, both equations may be solvable");
				printf("\n when 2*A3(A1*B2+A2*B1) = 0 mod A1*A2, yielding distinct (B3,e) pairs if |H1(M)| ≠ 0.");
				}
			if(Batch == FALSE && MyMinNumGenerators == 2 && MyMinNumRelators <= 2)
				{
				printf("\n\n Note 1) Heegaard only checks for Seifert fibrations of manifolds in Orbit 1 and manifolds");
				printf("\n in other orbits for which the 'Canonical Rep Presentation' is marked 'pseudo-minimal' or");
				printf("\n 'quasi-pseudo-minimal' or the 'Canonical Rep Presentation' is missing from the orbit list.");
				printf("\n or in Orbits < 100 with UDV[] == DONE.");
				printf("\n Note 2) Heegaard recognizes a Seifert manifold M from special features of M's presentation. Since");
				printf("\n only some presentations of M may exhibit these features, Heegaard looks at multiple presentations.");
				}
			}
		
		if(F1 != 2)	
			{	
			if(NumSFFound == 0 && Do_Not_Reduce_Genus == FALSE && !FoundBigSF)
				{
				/****** If no Seifert fibration was found, check for essential tori. ******/
	
				NonSFL = (int*) NewPtr((sizeof(int)*NumOrbits));
				if(NonSFL == NULL) Mem_Error();	
				for(k = NumSFChecked = n = 0; k < NumOrbits ; k++)
					{
					if(NumOrbits == 1)
						j = BeenChecked[0] - MAX_MIN_GEN_PRES;
					else
						j = Table2[k]; 
					for(i = 0; i < MyNumSavedPres; i++) if(BeenChecked[i] == j + MAX_MIN_GEN_PRES)
						{
						ReadPres 		= SUR_Num[i];
						NumGenerators 	= NG[ReadPres];
						NumRelators 	= NR[ReadPres];
						Vertices		= 2*NumGenerators;
						Length 			= SURL[ReadPres];
						MyOrbitSize     = OrbitSize[i];
						if(NumGenerators > 3) continue;
						if(NumRelators > 3) continue;
						if(NewRep[i] || PMQPML[i] || (k == 0) || F1 == 3)
							{					
							for(l = 1, Length = 0; l <= NumRelators; l++)
								{
								if(Relators[l] != NULL) DisposeHandle((char **) Relators[l]);
								Relators[l] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[i][l]));
								if(Relators[l] == NULL) Mem_Error();
								p = *Relators[l];
								q = *SMGP[i][l];
								while( (*p++ = *q++) ) ;
								Length += GetHandleSize((char **) Relators[l]) - 1;
								}
							NumSFChecked ++;						
							m = 0;
							if(NumGenerators == 3 && NumRelators == 3) m = Genus3ET(k+1,1,0);
							if(m)
								{
								FoundEssentialTorus = TRUE;
								if(B10B11Recognized) goto FOUND_TORUS;
								printf("\n\nThere is an essential torus in the manifold of Orbit %d.",k+1);
								n = m % 10;
								m -= n;
								m = m/10;
								char x;
								switch(n)
									{
									case 1:
										x = 'A';
										break;
									case 2:
										x = 'B';
										break;
									case 3:
										x = 'C';
									}
								printf("\nR%d is disjoint from cutting disk D_%c of the underlying handlebody H.",m,x);
								printf("\nIf h = H - D_%c and h' = H' - D_R%d, then T = Bdry h[R%d] = Bdry h'[Bdry D_%c] is an essential torus."
								,x,m,m,x);
								printf("\nBdry D_%c = %s",x,SETR4[1]);
								printf("\nHeegaard checked %d diagram(s).",NumSFChecked);
								goto FOUND_TORUS;							
								}
							if(k == 0 && NumRelators == 1 && NumGenerators == 2)
								{
								m = Genus_Two_One_Relator_Annuli_And_Tori(TRUE,TRUE);
								if(m == 0) 
									{
									printf("\n\nH[R] is anannular and atoroidal.");
									if(B10B11Recognized)
									fprintf(H_Results," H[R] is anannular and atoroidal.");
									}
								if(m == 1) 
									{
									FoundEssentialTorus = TRUE;
									goto FOUND_TORUS;
									}
								} 							
							if(NumRelators == 2 && NumGenerators == 2) 
								{							
								m = Genus_Two_Essential_Tori(k + 1,MyCompNum,0);
								if(m == 1) n++;
								if(m == 2)
									{
									FoundEssentialTorus = TRUE;
									if(B10B11Recognized) goto FOUND_TORUS;
									n++;
									printf("\n\nThere is an essential torus in the manifold of Orbit %d.",k+1);
									printf("\nHeegaard checked %d diagram(s) of which %d had a relator disjoint from a proper-power.",NumSFChecked,n);
									goto FOUND_TORUS;
									}							
								}
							}
						}
					}				
				}
			
	FOUND_TORUS:

			/******************************************************************************************
				If !Batch and no essential tori were found in diagrams of HS Reps, broaden the search.
			*******************************************************************************************/
			
			if(!Batch && NumSFFound == 0 && FoundEssentialTorus == FALSE && !FoundBigSF)
				{
				j = 0;
				if(MyMinNumGenerators == 3 && MyMinNumRelators == 3) 
					{
					k = Init_Genus_Three_Essential_Tori(MyTable,SNumFilled - 1,1,1);
					j = 1;
					}
				if(FoundEssentialTorus == FALSE && MyMinNumGenerators == 2 && MyMinNumRelators == 2)
					{
					k = Init_Genus_Two_Essential_Tori(MyTable,SNumFilled - 1,1,1);
					j = 1;
					}
				if(j && FoundEssentialTorus == FALSE) 
					printf("\n\nHeegaard checked %d diagrams and found no essential tori.",MyNumSavedPres);
				if(FoundEssentialTorus)
					printf("\n\nHeegaard checked %d diagrams for tori.",SNumFilled - k);	
				}

			if(B10B11Recognized && FoundEssentialTorus && (MyMinNumRelators > 1 || MyMinNumGenerators > 2)) 
				{
				Print_ET_Data(MyCompNum);
				goto END;
				}
			}
		}
			
	if(F1 != 2)	
		{
		if(Batch == FALSE && MyMinNumGenerators == 2 && MyMinNumRelators == 2) Init_Get_Universal_Minimizer_Waves(NumHSReps,HSRepL);											
		if(Batch == 4) Check_HS_Simple_Circuits(NumHSReps,HSRepL,HSL2);
		if(Batch == 53) Is_IP_In_HS_Reps(NumHSReps,HSRepL);
		
		if(Batch == FALSE)
			{
			printf("\n\nCHECK HS REDUCIBILITY, WEAK REDUCIBILITY, DISJOINT CURVE PROPERTY, STRONG IRREDUCIBILITY ? HIT 'X',x','Y','y' OR 'n'.");
			printf(" (Note hitting 'Y' turns Micro_Print on. See Check_HS_Strong_Irreducibility() source for info on 'X' and 'x'.)    ");
			GET_RESPONSE5:
			SMicro_Print = Micro_Print;
			switch(WaitkbHit())
				{
				case 'x':
					Micro_Print = 7;
				case 'X':
					if(Micro_Print != 7) Micro_Print = 6;
					if(HSL2) DisposePtr((char*) HSL2);
					HSL2 = (char *) NewPtr((sizeof(char)*(NumSplittings + 1)));
					if(HSL2 == NULL) Mem_Error();
					Check_HS_Strong_Irreducibility(NumHSReps,HSRepL,HSL2);
					break;
				case 'Y':
					Micro_Print = 5;
				case 'y':
					if(HSL2) DisposePtr((char*) HSL2);
					HSL2 = (char *) NewPtr((sizeof(char)*(NumSplittings + 1)));
					if(HSL2 == NULL) Mem_Error();
					for(i = 1; i <= NumSplittings; i++) HSL2[i] = FALSE;
					Check_HS_Reducibility(NumHSReps,HSRepL,HSL2);
					Check_HS_Weak_Reducibility(NumHSReps,HSRepL,HSL2);
					Check_HS_Simple_Circuits(NumHSReps,HSRepL,HSL2);
					Check_HS_Disjoint_Curves(NumHSReps,HSRepL,HSL2);
					Check_HS_Strong_Irreducibility(NumHSReps,HSRepL,HSL2);				
				case 'n':
					break;
				default:
					SysBeep(5);
					goto GET_RESPONSE5;			
				}
			Micro_Print = SMicro_Print;						
							
			printf("\n\nDISPLAY DIAGRAMS OF HEEGAARD SPLITTING REPS ? HIT 'y' OR 'n'.    ");
			GET_RESPONSE6:
			switch(WaitkbHit())
				{
				case 'y':
					printf("\n");
					Display_HS_Diagrams(NumHSReps,HSRepL);
					break;
				case 'n':
					break;
				default:
					if(Batch == FALSE) SysBeep(5);
					goto GET_RESPONSE6;
				}	
			}
		}	
		
	if(Batch == FALSE)
		{	
		printf("\n\nREWRITE SELECTED ORBIT REPS USING EXPONENTS ? HIT 'y' OR 'n'.    ");
		GET_RESPONSE7:
		switch(WaitkbHit())
			{
			case 'y':
				printf("\n");
				Rewrite_Orbit_Reps(MyMinNumRelators,NumOrbits,OrbitNum2SLRNum);
				break;
			case 'n':
				break;
			default:
				if(Batch == FALSE) SysBeep(5);
				goto GET_RESPONSE7;
			}
		printf("\n\nPRINT SELECTED ORBIT REPS ? HIT 'y' OR 'n'.    ");
		GET_RESPONSE8:
		switch(WaitkbHit())
			{
			case 'y':
				printf("\n");
				Print_Orbit_Reps(MyMinNumRelators,NumOrbits,OrbitNum2SLRNum);
				break;
			case 'n':
				break;
			default:
				if(Batch == FALSE) SysBeep(5);
				goto GET_RESPONSE8;
			}		
		}
		
END:		
	/*******************************************************************
				Delete presentations saved in SMGP[ ].
	*******************************************************************/
	
	Delete_Old_PresentationsSMGP(MyNumSavedPres, SUR_Num);
	
	if(Table2) 
		{
		DisposePtr((int*) Table2);
		Table2 = NULL;
		}
	if(Table3)
		{
		DisposePtr((int*) Table3);
		Table3 = NULL;
		}
	if(HSL) 				DisposePtr((unsigned int*) HSL);
	if(HSL2) 				DisposePtr((char*) HSL2);
	if(HSN)					DisposePtr((unsigned int*) HSN);
	if(HSRepL)				DisposePtr((int*) HSRepL);
	if(HegSplNumCount) 		DisposePtr((unsigned int*) HegSplNumCount);
	if(HegSplNumFirstOrbit)	DisposePtr((unsigned int*) HegSplNumFirstOrbit);
	if(HitSumL)				DisposePtr((int*) HitSumL);
	if(LoopSumL)			DisposePtr((int*) LoopSumL);
	if(OrbitLength)			DisposePtr((unsigned int*) OrbitLength);
	if(OrbitSize)			DisposePtr((unsigned int*) OrbitSize);
	if(OrbitNum2SLRNum)		DisposePtr((unsigned int*) OrbitNum2SLRNum);
	if(NewRep)				DisposePtr((unsigned char*) NewRep);
	if(PMQPML)				DisposePtr((char*) PMQPML);
	if(NonSFL) 				DisposePtr((int*) NonSFL);
	NumFilled = SNumFilled;	
if(QuitFlag) return(QUIT_FLAG);	
return(0);
}

unsigned int In_File2(int Test, unsigned char ***MyRelators)
{    
    unsigned char  *p,
    				*q,
    				*r;
                               
    int           	i,
    				Result;
    
    unsigned int  	Node;
    
    Size         	HSP,
    				HSQ;     
    
    if(Test)
    	{
    	for(i = 1; i <= NumRelators; i++) LR[i] = GetHandleSize((char **) MyRelators[i]) - 1;
    	}
    else
    	Canonical_Rewrite(Relators,FALSE,FALSE);

    Node = 0;
    while(1)
        {
        for(i = 1,Result = 0; i <= NumRelators; i++)
            {
         	HSP = LR[i] + 1;
            HSQ = GetHandleSize((char **) SLP[Node][i]);
            if(HSP > HSQ)
                {
                Result = 1;
                break;
                }
            if(HSP < HSQ)
                {
                Result = -1;
                break;
                }
            }
        if(Result == 0)    for(i = 1; i <= NumRelators; i++)
            {
            r = *MyRelators[i] + LR[i];
            *r = 125;
            for(p = *MyRelators[i],q = *SLP[Node][i]; *p == *q; p++,q++) ;
      	    *r = EOS;
            if(*p < *q)
                {
                Result = 1;
                break;
                }
            if(*p > *q)
                {
                Result = -1;
                break;
                }
            }        
        switch(Result)
            {
            case 1:
                if(Left[Node] == INFINITE)
                    {
                    if(Test) return(INFINITE);
                    if(Compute_Stabilizers)
                         printf("  %d -> %d",ReadPres + 1,NumFilled + 1);
                    if(Save_Pres2()) return(TOO_LONG);
                    Left[Node] = NumFilled - 1;
                    Left[NumFilled - 1] = Right[NumFilled - 1] = INFINITE;
                    return(NumFilled - 1);
                    }
                else
                    Node = Left[Node];
                break;        
            case 0:
                if(Compute_Stabilizers)
                     printf("  %d -> %d",ReadPres + 1,Node + 1);
                return(Node);
            case -1:
                if(Right[Node] == INFINITE)
                    {
                    if(Test) return(INFINITE);
                    if(Compute_Stabilizers)
                         printf("  %d -> %d",ReadPres + 1,NumFilled + 1);
                    if(Save_Pres2()) return(TOO_LONG);
                    Right[Node] = NumFilled - 1;
                    Left[NumFilled - 1] = Right[NumFilled - 1] = INFINITE;
                    return(NumFilled - 1);
                    }
                else
                    Node = Right[Node];
                break;            
            }
        }
}

int Save_Pres2(void)
{
    /******************************************************************************************
        Save_Pres2() is called from InFile2() when Heegaard has determined that a 
        presentation should be saved. It saves a copy of the presentation in the array
        SLP[][].
    ******************************************************************************************/
    
    unsigned char  *p,
                    *q;
                    
    int            i;
                        
	SLP[NumFilled] = (unsigned char ***) NewPtr(sizeof(long)*(NumRelators + 1));
	if(SLP[NumFilled] == NULL) Mem_Error();
			
    for(i = 1; i <= NumRelators; i++)
        {
        SLP[NumFilled][i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));            
        if(SLP[NumFilled][i] == NULL) Mem_Error();
        q = *SLP[NumFilled][i];    
        p = *Relators[i];
        while( (*q++ = *p++) ) ;                                    
        }

    NumFilled ++;
        
    if(Micro_Print == 1) printf("\n\nSaved the current presentation as: Presentation %u.\n",NumFilled);

    return(NO_ERROR);        
}	

void Delete_Old_PresentationsSLP(void)
{
    unsigned int    i,
                    j;
                            
    for(i = 0; i < NumFilled; i++)
        {
        for(j = 1; j <= NumRelators; j++) if(SLP[i][j] != NULL) 
        	{
        	DisposeHandle((char **) SLP[i][j]);
        	SLP[i][j] = NULL;
        	}
        if(SLP[i]) 
        	{
        	DisposePtr((char ***) SLP[i]);
        	SLP[i] = NULL;
        	}
        }
    NumFilled         = 0;
    BytesAvailable    = BYTES_AVAILABLE;
    BytesUsed         = 0L;
    UserSaidQuit      = FALSE;                    
}

void Delete_Old_PresentationsSMGP(int MyNumSavedPres,unsigned int* SUR_Num)
{
    unsigned int    i,
                    j;
                            
    for(i = 0; i < MyNumSavedPres; i++)
        {
        ReadPres = SUR_Num[i];
        NumRelators = NR[ReadPres];
        for(j = 1; j <= NumRelators; j++) if(SMGP[i][j] != NULL) 
        	{
        	DisposeHandle((char **) SMGP[i][j]);
        	SMGP[i][j] = NULL;
        	}
        }
    NumFilled         = 0;
    BytesAvailable    = BYTES_AVAILABLE;
    BytesUsed         = 0L;
    UserSaidQuit      = FALSE;                    
}

void qksort2(int first,int last,int NumRelators,unsigned int* SUR_Num)
{
	int 		i;		/*  "static" to save stack space  */
	int 		j;
	int         qkst_compare2();
    void        qkst_swap2();
 
	while (last - first > 1) 
		{
		i = first;
		j = last;
		for (;;) 
			{
			while (++i < last  && qkst_compare2(i, first, NumRelators, SUR_Num) < 0) 	;
			while (--j > first && qkst_compare2(j, first, NumRelators, SUR_Num) > 0)	;
			if (i >= j)	break;
			qkst_swap2(i, j);
			}
		qkst_swap2(first, j);
		if (j - first < last - (j + 1)) 
			{
			qksort2(first, j, NumRelators, SUR_Num);
			first = j + 1;					/*  qsort2(j + 1, last, NumRelators, SUR_Num);  */
			}
		else 
			{
			qksort2(j + 1, last, NumRelators, SUR_Num);
			last = j;						/*  qsort2(first, j, NumRelators, SUR_Num);  */
			}
		}
}

int qkst_compare2(int i,int j,int NumRelators,unsigned int* SUR_Num)
{
    unsigned char  	*p,
                    *q;
                            
    int           	Pi,
                    Pj,
                    k;
              
    Pi = Table3[Table2[i]];
    Pj = Table3[Table2[j]];
    if(Pi == Pj) return(0);

    if(SURL[SUR_Num[Pi]] < SURL[SUR_Num[Pj]]) return(-1);
    if(SURL[SUR_Num[Pi]] > SURL[SUR_Num[Pj]]) return(1);
    for(k = 1; k <= NumRelators; k++)
        {
        if(GetHandleSize((char **) SMGP[Pi][k]) > GetHandleSize((char **) SMGP[Pj][k])) return(-1);
        if(GetHandleSize((char **) SMGP[Pi][k]) < GetHandleSize((char **) SMGP[Pj][k])) return(1);
        }														
    for(k = 1; k <= NumRelators; k++)
        {
        p = *SMGP[Pi][k];
        q = *SMGP[Pj][k];
        while(*p && *p == *q)
            {
            p++;
            q++;
            }
        if(*p < *q) return(-1);
        if(*p > *q) return(1);
        }									
    return(0);
}	

void qkst_swap2(int i,int j)
{
    int            Temp;
    
    Temp          = Table2[i];
    Table2[i]     = Table2[j];
    Table2[j]     = Temp;
}

void ID_PMQPM(int MyNumSavedPres,char* PMQPML,unsigned int* SUR_Num)
{
	unsigned int	i,
					j,
					n;

	for(n = 0; n < MyNumSavedPres; n++) PMQPML[n] = FALSE;
	for(n = 0; n < MyNumSavedPres; n++)
		{
		i= SUR_Num[n];
		if(NR[i] == 1) PMQPML[n] = TRUE;
		else
			switch(UDV[i])
				{
				case SPLIT:		
				case GENERIC_LENS_SPACE:        	
				case THREE_SPHERE:	
				case NOT_CONNECTED:		
				case S1_X_S2:	
				case S1_X_D2:	
				case S1_X_X2:
				case MISSING_GEN_DONE2:		
				case MISSING_GEN_DONE1:		
				case KNOWN_LENS_SPACE:
					break;	
				case SEP_PAIRS:
					if(PRIM[i] >= 100) PMQPML[n] = TRUE;	                    
					break;	
				case ANNULUS_EXISTS:	
				case V2_ANNULUS_EXISTS:                	
				case DELETED_RELATOR:	
				case NON_UNIQUE_4:	
				case NON_UNIQUE_3:	
				case NON_UNIQUE_2:	
				case NON_UNIQUE_1:
					break;        	
				default:
					{
					j = PRIM[i];
					switch(j)
						{
						case 8:
						case 108:
							PMQPML[n] = TRUE;
							break;
						case 70:
						case 75:
							if(QPM[i]) PMQPML[n] = TRUE;
							break;    
						case 170:
						case 175:
							PMQPML[n] = TRUE;
							break;    
						default:
							if(j >= 100) PMQPML[n] = TRUE;
							if(QPM[i]) PMQPML[n] = TRUE;    
							break;
						}
					break;
					}                                                                                
				}
		if(n < MaxNumPMQPM && 0 < UDV[i] && UDV[i] <= DONE && PMQPML[n] == FALSE) PMQPML[n] = 2;		
		}
}

int ID_A_PMQPM(unsigned int i)
{
	unsigned int	j;

	if(NR[i] == 1) return(TRUE);
	else switch(UDV[i])
		{
		case SPLIT:		
		case GENERIC_LENS_SPACE:        	
		case THREE_SPHERE:	
		case NOT_CONNECTED:		
		case S1_X_S2:	
		case S1_X_D2:	
		case S1_X_X2:
		case MISSING_GEN_DONE2:		
		case MISSING_GEN_DONE1:		
		case KNOWN_LENS_SPACE:
			return(FALSE);	
		case SEP_PAIRS:
			if(PRIM[i] >= 100) return(TRUE);	
		case ANNULUS_EXISTS:	
		case V2_ANNULUS_EXISTS:                	
		case DELETED_RELATOR:	
		case NON_UNIQUE_4:	
		case NON_UNIQUE_3:	
		case NON_UNIQUE_2:	
		case NON_UNIQUE_1:
			return(FALSE);        	
		default:
			{
			j = PRIM[i];
			switch(j)
				{
				case 8:
				case 108:
					return(TRUE);
					break;
				case 70:
				case 75:
					if(QPM[i]) return(TRUE);
					break;    
				case 170:
				case 175:
					return(TRUE);
					break;    
				default:
					if(j >= 100) return(TRUE);
					if(QPM[i]) return(TRUE);    
					break;
				}
			break;
			}                                                                                
		}
	if(0 < UDV[i] && UDV[i] <= DONE) return(2);
	return(FALSE);	
}

int Rewrite_Orbit_Reps(int MyNumRelators,int NumOrbits,unsigned int* OrbitNum2SLRNum)
{	
	char			*ptr = NULL;
	
	unsigned char 	***MyRelators = NULL,
					*p,
					x,
					y;

	int				MyOrbit;

	unsigned int	ex,
					i,
					j;
	
	ptr = (char*) NewPtr(sizeof(char)*100);	
    if(ptr == NULL) Mem_Error();
             
    printf("\n\nEnter the number of an 'Orbit Rep' between 1 and %d you want rewritten. Then hit 'return'.", NumOrbits);
	printf("\nEnter 0 and hit 'return' to exit.\n\n    ");
START: 
	printf("Orbit ");   
GET_RESPONSE1:        
    ReadString((char *)ptr, GetPtrSize(ptr));
    sscanf((char *) ptr,"%d",&MyOrbit);
    if(MyOrbit == 0) 
    	{
    	DisposePtr((char *) ptr);
    	return(0);
    	}
    if(MyOrbit < 1 || MyOrbit > NumOrbits) goto GET_RESPONSE1;   
    j = OrbitNum2SLRNum[MyOrbit];
    MyRelators = SMGP[j];
    printf("\nRep of Orbit %d:", MyOrbit);
	for(i = 1; i <= MyNumRelators; i++)
		{
		printf("\n");
		p = *MyRelators[i];
		x = *p++;
		if(!x) continue;			/* Relators[i] is empty!  */
		ex = 1;
		while(*p == x)
			{
			ex++;
			p++;
			}
		printf("%c",x);	
		if(ex > 1) printf("^%d",ex);
		ex = 0;
		if(*p) x = *p;
		else continue; 			/* Relators[i] is a proper power!  */
		while( (y = *p++) )
			{
			if(x == y)
				ex++;
			else
				{
				printf("%c",x);
				if(ex > 1) printf("^%d",ex);	
				ex = 1;    
				}
			x = y;
			}
		printf("%c",x);
		if(ex > 1) printf("^%d",ex);
		}
	printf("\n\n");		
	goto START;
}

int Print_Orbit_Reps(int MyNumRelators,int NumOrbits,unsigned int* OrbitNum2SLRNum)
{	
	char			*ptr = NULL;
	
	unsigned char 	***MyRelators = NULL;

	int				MyOrbit;

	unsigned int	i,
					j;
	
	ptr = (char*) NewPtr(sizeof(char)*100);	
    if(ptr == NULL) Mem_Error();
             
    printf("\n\nEnter orbit reps 1 X 1 from 1 to %d you want printed while hitting 'return', or enter '0' and hit 'return' to exit.    \n\n", NumOrbits);
START: 
	printf("Orbit ");   	
GET_RESPONSE1:        
    ReadString((char *)ptr, GetPtrSize(ptr));
    sscanf((char *) ptr,"%d",&MyOrbit);
    if(MyOrbit == 0) 
    	{
    	DisposePtr((char *) ptr);
    	return(0);
    	}
    if(MyOrbit < 1 || MyOrbit > NumOrbits) goto GET_RESPONSE1;   
    j = OrbitNum2SLRNum[MyOrbit];
    MyRelators = SMGP[j];
	printf("    %s",*MyRelators[1]);
	for(i = 2; i <= MyNumRelators; i++) printf("\n    %s",*MyRelators[i]);
	printf("\n\n");		
	goto START;
}

void MergeHegSpl(unsigned int i,unsigned int j)
{ 
	unsigned int	ii,
					jj,
					k;
				
	if(NG[i] == NG[j] && ComponentNum[i] == ComponentNum[j])
		{
		if(HegSplNum[i] < HegSplNum[j])
			{
			ii = HegSplNum[i];
			jj = HegSplNum[j];
			k = j;
			while(1)
				{
				if(HegSplNum[k] == ii) break;
				HegSplNum[k] = ii;
				k = HegSplNxt[k];
				}
			ii = HegSplNxt[i];
			jj = HegSplNxt[j];
			HegSplNxt[j] = ii;
			HegSplNxt[i] = jj;	
			Mergers ++;
			}
		if(HegSplNum[i] > HegSplNum[j])
			{
			ii = HegSplNum[i];
			jj = HegSplNum[j];
			k = i;
			while(1)
				{
				if(HegSplNum[k] == jj) break;
				HegSplNum[k] = jj;
				k = HegSplNxt[k];
				}
			ii = HegSplNxt[i];
			jj = HegSplNxt[j];
			HegSplNxt[j] = ii;
			HegSplNxt[i] = jj;
			Mergers ++;
			}			
		}        
}

int Display_HS_Diagrams(int NumHSReps,int* HSRepL)
{
	unsigned char	*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m;
	
	printf("\n");
	for(i = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{
			j = -HSRepL[i];
			k = 1;
			continue;
			}
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new and needs to be checked for annuli and uniqueness. */
			printf("\nPres %d of HS %d is new.",k,j);
			l = HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			WhichInput		= MAX_SAVED_PRES - 1;
			UDV[WhichInput] = 0;
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
			if(Display_A_Diagram(TRUE,k,j) == 2) return(2);	
			k++;		
			}
		else 
			{
			WhichInput = HSRepL[i];
			if(Display_A_Diagram(TRUE,k,j) == 2) return(2);
			k++;
			}
		}
		
	return(0);	
}

void Check_HS_Uniqueness(int NumHSReps,int* HSRepL)
{
	unsigned char	*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m,
					NumBad;
				
	printf("\n\n	Making sure each Heegaard Splitting Representative Presentation has been checked...\n");
	
	for(i = NumBad = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{
			j = -HSRepL[i];
			k = 1;
			continue;
			}
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new and needs to be checked for annuli and uniqueness. */
			l 				= HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
				
			if(Check_HS_Uniqueness_Sub1(j,k)) NumBad ++;
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
			
			if(Check_HS_Uniqueness_Sub1(j,k)) NumBad ++;
			k++;
			}
		}
		
	if(NumBad == 0) 
		{
		if(Batch == FALSE) printf("\n\n");
		printf("	Each Heegaard Splitting Representative Presentation has a unique realization.");
		}	
}

int Check_HS_Uniqueness_Sub1(int MyHSNum,int MyPresNum)
{
	int				i,
					j,
					k,
					LTRV;
				
	unsigned int	DMRV;
			
	long			HSS;

	unsigned int	Diagram_Main();			
	
	if(Length == 0 || NumGenerators == 0 || NumRelators == 0) 
		{
		printf("\nPres %d of Heegaard-Splitting %d is empty!",MyPresNum,MyHSNum);
		return(1);
		}
		
	if(NumGenerators == 1)
		{
		if(NumRelators == 1 && GetHandleSize((char **) Relators[1]) > 4)
			{
			printf("\nPres %d of Heegaard-Splitting %d does not have a unique realization.",MyPresNum,MyHSNum);
			return(1);
			}
		if(NumRelators > 1)
			{
			HSS = GetHandleSize((char **) Relators[1]);
			for(i = 2; i <= NumRelators; i++) if(HSS != GetHandleSize((char **) Relators[i]))
				{
				printf("\nPres %d of Heegaard-Splitting %d is not realizable.",MyPresNum,MyHSNum);
				return(1);
				}
			if(HSS > 4)
				{
				printf("\nPres %d of Heegaard-Splitting %d does not have a unique realization.",MyPresNum,MyHSNum);
				return(1);
				}				
			}	
		}	

	Num_Level_Slides = 0;
	
RETRY:

	Fill_A(NumRelators);
    
    /****************************************************************************************** 
            Set VWG[i] equal to the valence of vertex i in the "reduced" Whitehead graph. 
            Set NumEdges equal to the number of edges in the "reduced" Whitehead graph.
            Use A[][] to setup AJ1[][].
    ******************************************************************************************/
    
    for(i = NumEdges = 0;i < Vertices; i ++)
        {
        A[i][i] = 0;
        for(j = k = 0; j < Vertices; j ++) if(A[i][j])
            {
            AJ1[i][k] = j;
            k++;
            }
        VWG[i] = k;
        NumEdges += k;
        AJ1[i][k] = VERTICES;
        }                            
    NumEdges /= 2;
	
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;
 	if(Connected_(0,0) == FALSE)
 		{
		printf("\nThe Whitehead Graph of Pres %d of Heegaard-Splitting %d is not connected.",MyPresNum,MyHSNum);
		return(1);		
		}
		
	SepPairs = Sep_Pairs(0,0,1);
	
	if(SepPairs)
		{
		printf("\nThe Whitehead Graph of Pres %d of Heegaard-Splitting %d has a separating pair of vertices.",MyPresNum,MyHSNum);
		Num_Level_Slides = 0;
		Num_Saved_LPres  = 0;
		NotNewPres		 = 0;
		TestRealizability4 = TRUE;
		LTRV = Level_Transformations(0,0,1);
		TestRealizability4 = FALSE;
		switch(LTRV)
			{
			case 0: return(1);
			case 2: goto RETRY;
			case 3:
				{
				printf("\nPres %d of Heegaard-Splitting %d is not realizable.",MyPresNum,MyHSNum);
                return(1);				
				}
			case 13:
				{
				if(Num_Level_Slides == 0) printf("\nHeegaard found an annulus in Pres %d of Heegaard-Splitting %d.",MyPresNum,MyHSNum);
				if(Num_Level_Slides == 1) 
					printf("\nAfter %lu Sep-Vert-Slide, an annulus exists in a presentation obtained from Pres %d of Heegaard-Splitting %d."
					,Num_Level_Slides,MyPresNum,MyHSNum);
				if(Num_Level_Slides > 1)
					printf("\nAfter %lu Sep-Vert-Slides, an annulus exists in a presentation obtained from Pres %d of Heegaard-Splitting %d."
					,Num_Level_Slides,MyPresNum,MyHSNum);	
				printf("\nRerun Pres %d of Heegaard-Splitting %d for details.",MyPresNum,MyHSNum);
				return(1);
				}				
			case 6:
				{
				printf("\nThe search for level-transformations of Pres %d of Heegaard-Splitting %d was interrupted.",MyPresNum,MyHSNum);
				return(1);
				}
			case TOO_LONG:
				{
				printf("\nAn error occurred when checking Pres %d of Heegaard-Splitting %d. Perhaps the presentation is too long.",MyPresNum,MyHSNum);
                return(1);
                }		
			}			
		}
	else
		{
		if(Planar(TRUE,FALSE))
			{
			printf("\nThe Whitehead Graph of Pres %d of Heegaard-Splitting %d is not planar.",MyPresNum,MyHSNum);
			return(1);			
			}
		TestRealizability4 = TRUE;
		DMRV = Diagram_Main();
		TestRealizability4 = FALSE;
		switch(DMRV)
			{
			case NO_ERROR:
				{
				if(Num_Level_Slides == 1)
					printf("\nAfter %lu Sep-Vert-Slide, Pres %d of Heegaard-Splitting %d is uniquely realizable.",
					Num_Level_Slides,MyPresNum,MyHSNum);				
				if(Num_Level_Slides > 1)
					printf("\nAfter %lu Sep-Vert-Slides, Pres %d of Heegaard-Splitting %d is uniquely realizable.",
					Num_Level_Slides,MyPresNum,MyHSNum);
				return(0);
				}
			case NON_UNIQUE_1:
				{
				printf("\nThe diagram of Pres %d of Heegaard-Splitting %d is not unique because there is a generator which",MyPresNum,MyHSNum);
                printf("\nappears with only one exponent, either 3,4 or 6, and a needed symmetry does not exist.");
				return(1);
				}
			case NON_UNIQUE_2:
				{
				printf("\nThe diagram of Pres %d of Heegaard-Splitting %d is not unique because there is a generator which",MyPresNum,MyHSNum);
                printf("\nappears only with exponent 3 or only with exponent 4 and this exponent occurs more than once.");
				return(1);
				}
			case NON_UNIQUE_3:
				{
				printf("\nThe diagram of Pres %d of Heegaard-Splitting %d is not unique because there is a generator which",MyPresNum,MyHSNum);
                printf("\nappears only with exponent 5.");
                return(1);
				}
			case NON_UNIQUE_4:
				{
				printf("\nThe diagram of Pres %d of Heegaard-Splitting %d is not unique because there is a generator which",MyPresNum,MyHSNum);
                printf("\nappears with only one exponent and that exponent is greater than 6.");
                return(1);
				}
			case V2_ANNULUS_EXISTS:
				{
				printf("\nThe diagram of Pres %d of Heegaard-Splitting %d is not unique because it has a valence two annulus.",MyPresNum,MyHSNum);
                return(1);				
				}
			case FATAL_ERROR:
				{
				printf("\nPres %d of Heegaard-Splitting %d is not realizable.",MyPresNum,MyHSNum);
                return(1);				
				}	
			case TOO_LONG:
				{
				printf("\nAn error occurred when checking Pres %d of Heegaard-Splitting %d. Perhaps the presentation is too long.",MyPresNum,MyHSNum);
                return(1);				
				}	
			}
		}
	return(0);			
}

int Check_HS_Simple_Circuits(int NumHSReps,int* HSRepL,char* HSL2)
{
	unsigned char	*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m,
					NumDisjointCurves,
					NumPresChecked = 0;
	
	for(i = NumDisjointCurves = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{
			j = -HSRepL[i];
			k = 1;
			continue;
			}
		if(HSL2[j]) continue;
		if(NumDisjointCurves == 0) NumDisjointCurves = 1;
		NumPresChecked ++;	
		if(HSRepL[i] >= INFINITE)
			{			
			/* The canonical rep presentation is new and needs to be checked for annuli and uniqueness. */
			l = HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];		
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			WhichInput		= MAX_SAVED_PRES - 1;
			UDV[WhichInput] = 0;						
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
			if(Find_Simple_Circuits()) 
				{
				HSL2[j] = 3;
				if(NumDisjointCurves > 1)
					printf(", Pres %d of HS %d",k,j);
				else
					{
					printf("\nThere are primitives, proper-powers, or curves not of full rank disjoint from the relators of:");
					printf(" Pres %d of HS %d. Hence HS %d is a distance <= 2 splitting.",k,j,j);
					NumDisjointCurves ++;
					}
				}
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			WhichInput 		= HSRepL[i];
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
				
			if(Find_Simple_Circuits())
				{
				HSL2[j] = 3;
				if(NumDisjointCurves > 1)
					printf(", Pres %d of HS %d",k,j);
				else
					{
					printf("\nThere are primitives, proper-powers, or curves not of full rank disjoint from the relators of:");
					printf(" Pres %d of HS %d. Hence HS %d is a distance <= 2 splitting.",k,j,j);
					NumDisjointCurves ++;
					}
				}
			k++;
			}
		}
	
	if(NumDisjointCurves == 1) 
		printf("\nChecked %d HS Rep(s). Found no simple circuit with less than full-rank disjoint from the full set of relators of any HS Rep.",NumPresChecked);	
	if(NumDisjointCurves > 1)
		printf("\nCheck paths and simple circuits of diagrams of the HS presentations for details.");		
		
	return(0);		
}

int Find_Simple_Circuits(void)
{
	/********************************************************************************************
		Find_Simple_Circuits() finds each 'simple' circuit disjoint from the relators in the 
		Heegaard diagram and checks if it is primitive, a proper-power, or less than full rank.
	********************************************************************************************/							
							
	unsigned char 	*FacesVisited = NULL,
					*FacesVisitedList = NULL,
					InitialFace,
					NumPathsInCircuit,
					*p,
					**PM = NULL,
					*PM_From = NULL,
					*PM_To = NULL,
					**PP = NULL,
					*PP_From = NULL,
					*PP_To = NULL,
					PossibleNewTerminalFace,
					*q,
					*r,
					*SRelator1 = NULL,
					TerminalFace,
					*T2 = NULL,
					tl,
					tr,
					V1,
					V2,
					V3,
					V4,
					x;
													
	int 			Big_Number = 50000,
					Error,
					ii,
					*PathsInCircuit = NULL,
					**P_From_Face = NULL,
					*pp,
					ss,
					SNumGenerators,
					SNumRelators;
							
	unsigned int 	c,
					d,
					e,
					edge,
					EL[6*VERTICES],
					ee,
					h,
					i,
					j,
					k,
					NumCircuitsFound,
					NumNotFullRank,
					NumPaths,
					v,
					vertex,
					vertexRS,
					vertexLE,
					w;
	
	long 			HSS = 0,
					length;
	
	unsigned long	max;
	
	Error = 0;
	NumPaths = 0;
	
	Fill_A(NumRelators);				
	if(ComputeValences_A()) return(0);
	Get_Matrix();
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;
	if(Connected_(0,0) == FALSE) return(0);
	if(Sep_Pairs(0,0,1)) return(0);
	if(Planar(FALSE,TRUE) == TRUE) return(0);
	if(Diagram_Main()) return(0);

	PM = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PM == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PM[d] = NULL;	
	PP = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PP == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PP[d] = NULL;
	P_From_Face = (int **) NewPtr(sizeof(long)*(NumFaces + 1));
	if(P_From_Face == NULL) Mem_Error();
	for(d = 1; d <= NumFaces; d++) P_From_Face[d] = NULL;	
	PM_From = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PM_From == NULL) Mem_Error();
	PP_From = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_From == NULL) Mem_Error();
	PM_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PM_To == NULL) Mem_Error();
	PP_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_To == NULL) Mem_Error();
	PathsInCircuit = (int *) NewPtr(sizeof(int)*(NumFaces + 2));
	if(PathsInCircuit == NULL) Mem_Error();
	FacesVisitedList = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 2));
	if(FacesVisitedList == NULL) Mem_Error();
	FacesVisited = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 1));
	if(FacesVisited == NULL) Mem_Error();

	for(d = 1,max = 0L; d <= NumRelators; d++) if(LR[d] > max) max = LR[d];
	T2 = (unsigned char *) NewPtr(max + 2);
	if(T2 == NULL) Mem_Error();	
	for(d = 1; d <= 2*NumEdges; d++) EL[d] = d;
	NumPaths = 0;
					
	for(ss = 2*NumEdges; ss > 0; ss --)
		{		
		/**************************************************************************************
			Determine which edges of the original diagram are joined by the edge ss of the dual
			diagram.
		**************************************************************************************/	
		
		for(v = c = 0; c + VWG[v] < EL[ss]; v++) c += VWG[v];
		w = EL[ss] - c;
		for(c = ee = 0,vertexLE = d = FV[v]; c < w; c++)
			{
			ee += A[v][d];
			vertexLE = d;
			d = CO[v][d];
			}
		e = ee - 1;
		if(v & 1)
			{	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			if(e) e--;
			else e = V[v] - 1;
			}
		
		p = q = *DualRelators[(v >> 1) + 1] + e;
		q++;
		if(!*q) q = *DualRelators[(v >> 1) + 1];
		if(v & 1)
			{
			tr = *p;
			tl = *q;
			if(tr > 95) tr -= 32;
			else tr += 32;
			}
		else
			{
			tl = *p;
			tr = *q;
			if(tl > 95) tl -= 32;
			else tl += 32;
			}		
		
		length	= 0L;
		vertex  = v;
		V2 		= vertex;
		edge    = ee % V[v];
		e 		= edge;
		r		= T2;
		
		/**************************************************************************************
			Two relators have come from distinct vertices and are adjacent to each other at
			vertex v. Follow these two relators along until they diverge. The region where
			they are parallel is the "cancellation region".
		**************************************************************************************/	
		
		do
			{
			if(v & 1)
				{
				*r = (v >> 1) + 97;
				w = v - 1;
				}
			else
				{
				*r = (v >> 1) + 65;
				w = v + 1;
				}
			V4 = v;	
			r++;	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			length ++;
			if(length > max)
				{			
				Error = 2;
				goto END;
				}	
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}	
			if(e == (d - 1))	
				{
				/***********************************************************************
					If e = d - 1, then we have found the end of the cancellation region.
				***********************************************************************/
				
				*r++ = EOS;
				if(V4 & 1)
					V4 -= 1;
				else
					V4 += 1;
				vertexRS = v;
				
				/***********************************************************************
					Determine which edge of the dual diagram corresponds to the end of
					the cancellation region and delete it from the list of available
					edges.
				***********************************************************************/	
				
				for(d = 0,c = 1; d < w; d++) c += VWG[d];
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					c++;
					v = CO[w][v];
					d += A[w][v];
					}
				if(EL[c] == c)
					{
					ss --;
					v = EL[ss];
					EL[ss] = c;
					EL[c] = v;
					}	
				else
					{
					for(d = 1; d < ss && (EL[d] != c); d++) ;
					if(d < ss)
						{
						ss --;
						v = EL[ss];
						EL[ss] = c;
						EL[d] = v;
						}
					}
				if(vertexLE & 1)
					x = (vertexLE >> 1) + 97;
				else
					x = (vertexLE >> 1) + 65;
				V1 = vertexLE;
				V3 = vertexRS;
				
				HSS = r - T2;
				NumPaths ++;
				
				PP[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PP[NumPaths] == NULL) Mem_Error();
				q = PP[NumPaths];	
				p = T2;
				while( (*q++ = *p++) ) ;

				PM[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PM[NumPaths] == NULL) Mem_Error();
				Inverse(PP[NumPaths]);
				q = PM[NumPaths];	
				p = PP[NumPaths];
				while( (*q++ = *p++) ) ;
				Inverse(PP[NumPaths]);
							
				/***********************************************************************************
							Identify the initial and terminal faces of this path.
				***********************************************************************************/
				
				for(h = 1,i = FALSE; h <= NumFaces; h++)
					{
					p = Face[h];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V1)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[h];
							if(*q == V2)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}
					
				for(j = 1,i = FALSE; j <= NumFaces; j++)
					{
					p = Face[j];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V3)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[j];
							if(*q == V4)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}

				PP_From[NumPaths] = h;
				PP_To[NumPaths]   = j;
				PM_From[NumPaths] = j;
				PM_To[NumPaths]   = h;
						
				break;
				}
			e = B[w][v] - e;
			}	
		while(v != vertex || e != edge);	
	}
	
	DisposePtr((char *) T2);

	for(i = 1; i <= NumFaces; i++)
		{
		p = Face[i];
		j = 2;
		while(*p++ < VERTICES) j++;
		P_From_Face[i] = (int *)NewPtr(sizeof(int)*j);
		if(P_From_Face[i] == NULL) Mem_Error();
		P_From_Face[i][0] = 1;
		P_From_Face[i][j-1] = Big_Number;
		for(h = 1; h < j-1; h++) P_From_Face[i][h] = 0;	
		}
				
	for(ii = 1; ii <= NumPaths; ii++)
		{
		pp = P_From_Face[PP_From[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = ii;
		pp = P_From_Face[PP_To[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = -ii;	
		}	
		
	/* Save copies of Relators[1], NumGenerators, and NumRelators. */
	
	SNumGenerators = NumGenerators;
	SNumRelators   = NumRelators;
	
	if(Relators[1] != NULL)
		{
		SRelator1 = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[1]));
		if(SRelator1 == NULL) Mem_Error();		
		p = *Relators[1];
		q = SRelator1;
		while((*q++ = *p++)) ;	
		}

	for(i = 1; i <= NumFaces; i++) FacesVisited[i] = FALSE;
	for(i = 1,NumCircuitsFound = NumNotFullRank = 0; i <= NumFaces; i++)
		{
		InitialFace = i;
		TerminalFace = i;
		NumPathsInCircuit = 0;
		for(j = 1; j <= InitialFace; j++) FacesVisited[j] = TRUE;
		FacesVisitedList[1] = InitialFace;
		while(1)
			{
			h = P_From_Face[TerminalFace][0];
			P_From_Face[TerminalFace][0] ++;
			ii = P_From_Face[TerminalFace][h];
			if(ii == Big_Number)
				{
				/*  We've reached a dead end. No new path from the current terminal face leads to a new face.
					Clear info for the current terminal face and reset the terminal face to the previous face. 	*/ 

				P_From_Face[TerminalFace][0] = 1;
				FacesVisited[TerminalFace] = FALSE;
				if(NumPathsInCircuit == 0) break; 
				NumPathsInCircuit --;
				TerminalFace = FacesVisitedList[NumPathsInCircuit + 1];		
				continue;
				}
			if(ii != Big_Number)
				{
				if(ii > 0) PossibleNewTerminalFace = PP_To[ii];
				if(ii < 0) PossibleNewTerminalFace = PM_To[-ii];
				if(PossibleNewTerminalFace < InitialFace) continue;
				if(PossibleNewTerminalFace == InitialFace)
					{
					if((NumPathsInCircuit == 0) && (ii < 0)) continue;
					if((NumPathsInCircuit > 0) && (ii == -PathsInCircuit[1])) continue;
					if((NumPathsInCircuit > 1) && (TerminalFace < FacesVisitedList[2])) continue;
					if((NumPathsInCircuit == 1) && (abs(ii) < abs(PathsInCircuit[1]))) continue;
					NumPathsInCircuit ++;
					PathsInCircuit[NumPathsInCircuit] = ii;
					NumCircuitsFound ++;										
					k = CHSP_Check_Simple_Circuits(NumCircuitsFound,PathsInCircuit,NumPathsInCircuit,PP,PM);	
					switch(k)
						{
						case 1:
						case 2:
						case 3:
							{
							NumNotFullRank ++;
							if(Micro_Print == 5) goto FOUND_NOT_FULL_RANK;
				/*			printf(" Circuit Faces and Paths: ");
							for(j = 1; j <= NumPathsInCircuit; j++) 
								printf("F%d,P%d,",FacesVisitedList[j],PathsInCircuit[j]);
								printf("F%d", PossibleNewTerminalFace);						*/
							}
						}	
					NumPathsInCircuit --;
					continue;	
					}		
		
				if((PossibleNewTerminalFace > InitialFace) && (FacesVisited[PossibleNewTerminalFace] == FALSE))
					{
					TerminalFace = PossibleNewTerminalFace;
					NumPathsInCircuit ++;
					PathsInCircuit[NumPathsInCircuit] = ii;
					FacesVisited[TerminalFace] = TRUE;
					FacesVisitedList[NumPathsInCircuit + 1] = TerminalFace;
					}
				}			
			}	
		}

FOUND_NOT_FULL_RANK:
		
	/* Restore Relators[1], NumGenerators and NumRelators. */
	
	NumGenerators = SNumGenerators;
	NumRelators   = SNumRelators;
	
	if(SRelator1 != NULL)
		{
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetPtrSize((char *) SRelator1));
		if(Relators[1] == NULL) Mem_Error();		
		p = SRelator1;
		q = *Relators[1];
		while((*q++ = *p++)) ;	
		DisposePtr((unsigned char *) SRelator1);
		}
		
END:

	for(j = 1; j <= NumPaths; j++) 
		{
		if(PM[j] != NULL) DisposePtr((char *) PM[j]);
		if(PP[j] != NULL) DisposePtr((char *) PP[j]);		
		}

	for(j = 1; j <= NumFaces; j++) if(P_From_Face[j]) DisposePtr((int *) P_From_Face[j]);
	if(PM != NULL) 					DisposePtr((unsigned char **) PM);
	if(PP != NULL) 					DisposePtr((unsigned char **) PP);	
	if(P_From_Face != NULL) 		DisposePtr((int **) P_From_Face);
	if(PM_From != NULL) 			DisposePtr((unsigned char *)  PM_From);
	if(PP_From != NULL) 			DisposePtr((unsigned char *)  PP_From);
	if(PM_To != NULL) 				DisposePtr((unsigned char *)  PM_To);
	if(PP_To != NULL) 				DisposePtr((unsigned char *)  PP_To);
	if(PathsInCircuit != NULL) 		DisposePtr((int *) PathsInCircuit);
	if(FacesVisitedList != NULL) 	DisposePtr((unsigned char *) FacesVisitedList);
	if(FacesVisited != NULL) 		DisposePtr((unsigned char *) FacesVisited);

if(NumNotFullRank > 0) return(1);	
return(0);	
}

int CHSP_Check_Simple_Circuits(unsigned int NCF,int* My_PathsInCircuit,int NumPaths,unsigned char** MyPP,
	unsigned char** MyPM)
{
	unsigned char	*p,
					*q;
					
	int				i,
					j,
					k,
					SNumGenerators;
					
	unsigned int	C[125];					
	
	unsigned long	HS;	

	for(i = 1,HS = 1L; i <= NumPaths; i++)	
		{
		j   = abs(My_PathsInCircuit[i]);
		HS += GetPtrSize((char *) MyPP[j]);
		}
	HS -= NumPaths;	
	if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
	Relators[1] = (unsigned char **) NewHandle(HS);
	if(Relators[1] == NULL) Mem_Error();
	q = *Relators[1];	
	for(i = 1; i <= NumPaths; i++)
		{
		j = My_PathsInCircuit[i];
		if(j > 0)
			{
			p = MyPP[j];
			while( (*q++ = *p++) ) ;
			q--;
			}
		else
			{
			p = MyPM[-j];
			while( (*q++ = *p++) ) ;
			q--;
			}	
		}
	
	SNumGenerators = NumGenerators;
	NumRelators = 1;

	switch(CheckPrimitivity())
		{
		case -1:
			{
			NumGenerators = SNumGenerators;
			return(2);	/* Relators[1] is a proper power. */			
			}
		case  0: 
			/************************************************************
			 Check if Relators[1] has full-rank or less than full-rank.
			*************************************************************/	
			for(i = 0; i < SNumGenerators; i++) C[i+'A'] = C[i+'a'] = 0;
			p = *Relators[1];
			while(*p)
				C[*p++]++;
			for(i = j = k = 0; i < SNumGenerators; i++,j+=2)
				{
				C[i+'A'] += C[i+'a'];
				C[j] = C[i+'A'];
				if(C[j] == 1) 
					{
					NumGenerators = SNumGenerators;
					return(1);	/* Relators[1] is a defining relator. */
					}
				if(C[j]) k++;
				}
			if(k == 1) 
				{
				NumGenerators = SNumGenerators;
				return(2);	/* Relators[1] is a proper power. */			
				}
			if(k < SNumGenerators)
				{
				NumGenerators = SNumGenerators;
				return(3);	/* Relators[1] is less than full-rank. */			
				}
			if(k == SNumGenerators)
				{
				NumGenerators = SNumGenerators;
				return(0);	/* Relators[1] has full rank. */			
				}			
			break;
		case  1:
			{
			NumGenerators = SNumGenerators;
			return(1);	/* Relators[1] is a primitive. */
			}
		case  TOO_LONG:
			break;
		}
		
	return(0);	
}

int Check_HS_Reps(int NumHSReps,int* HSRepL)
{
	unsigned char   *p,
                    *q;
    
    unsigned int    i,
                    k,
                    l,
                    m; 
    
    /******************************************************************************************
    				  Compare HS P1 with that saved in Copy_Of_Input[].
    ******************************************************************************************/
    
    CheckHSReps = FALSE;
    
 	for(i = 0; i < NumHSReps; i++)
		{		
		if(HSRepL[i] < 0) 
			{
			k = 1;
			continue;
			}
		if((i > 1) && Get_Next_Presentation_From_File(TRUE)) return(1);
		if(HSRepL[i] >= INFINITE)
			{
			/* The canonical rep presentation is new. */
			l = HSRepL[i] - INFINITE;
			ReadPres = SUR_Num[l];
			if(NumRelators != NR[ReadPres]) return(1);						
			for(m = 1; m <= NumRelators; m++)
				{
				p = *SMGP[l][m];
				if(i == 1)
					q = *Copy_Of_Input[m];
				else
					q = *Relators[m];
				while(*p && (*q++ == *p++) ) ;
				if((*p == EOS) && (*q == EOS)) continue;
				else
					{
					if(Batch == FALSE) SysBeep(5);
					printf("\n\nNote: Presentation HS 1 P %d does not match that in Heegaard_Input_Presentations!",k);
					return(1);
					}
				}
			k++;		
			}
		else 
			{
			ReadPres = HSRepL[i];
			if(NumRelators != NR[ReadPres]) return(1);			
			for(m = 1; m <= NumRelators; m++)
				{
				p = *SUR[ReadPres][m];
				if(i == 1)
					q = *Copy_Of_Input[m];
				else
					q = *Relators[m];				
				while(*p && (*q++ == *p++) ) ;
				if((*p == EOS) && (*q == EOS)) continue;
				else
					{
					if(Batch == FALSE) SysBeep(5);
					printf("\n\nNote: Presentation HS 1 P %d does not match that in Heegaard_Input_Presentations!",k);
					return(1);
					}
				}
			k++;
			}
		}
	printf("\n\nThe new HS Reps match the original HS Reps in Heegaard_Input_Presentations!");
	return(0);
}

int Get_Next_Presentation_From_File(char Flag)
{
    unsigned char  *p,
                    *q,
                    t;                                     
    
    unsigned int   	h,
                    i,
                    j;
                            
    long          	StrLength;

TOP:      

	/******************************************************************************************
		Look for the next nonempty line. This should be the identifier of the next Pres.
	******************************************************************************************/	
	
	do
		if(fgets((char *) Inst,MAXLENGTH,input_relators) == NULL) return(1);
	while(*Inst == '\n' || *Inst == '\r');
	
	p = Inst;
	while(1)
		{
		t = *p;
        if(t == '\n' || t == EOS || t == '\r')
            {
            *p = EOS;
            break;
            }
        p++;
        } 
        
    q = Inst;
    if((p - q) >= MAXLENGTH) goto TOP;
    
    /******************************************************************************************
    		Check that Inst is not just a string of '-'s, '*'s, ' 's or '\t's.
    ******************************************************************************************/ 
    
    p = Inst;
    while(1)
    	{
    	if(*p == EOS) break;
    	if(*p != '-') break;
    	p++;
    	}
    if(*p == EOS) goto TOP;
    p = Inst;
    while(1)
    	{
    	if(*p == EOS) break;
    	if(*p != '*') break;
    	p++;
    	}
    if(*p == EOS) goto TOP;
    p = Inst;
    while(1)
    	{
    	if(*p == EOS) break;
    	if(*p != ' ' && *p != '\t') break;
    	p++;
    	}
    if(*p == EOS) goto TOP;    
    q = Inst;  
    p = PresName;
    while((*p++ = *q++)) ;    
    
    /******************************************************************************************
    	Get the next line. This should be the first relator of the next Pres.
    ******************************************************************************************/   
    
    if(fgets((char *) Inst,MAXLENGTH,input_relators) == NULL) return(2);
    
    /******************************************************************************************
    	If the line following the supposed PresName is empty, go to the TOP.
    ******************************************************************************************/
        
    if(*Inst == '\n' || *Inst == '\r') goto TOP;

    /******************************************************************************************
        Read in the relators, at one relator to each nonempty line, stripping off leading 
        spaces and tabs.
    ******************************************************************************************/

    for(i = 1,NumRelators = 0; i <= MAXNUMRELATORS; i++)
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
            break;
            }
        j = 0;       
        while( (t = *p) )
            {
            if(t == '\n' || t == ' ' || t == '\t')
                {
                *p = EOS;
                break;
                }
            j++;
            if(!isalpha(t))
            	{
				/******************************************************************************
					The current line is not a relator. Look for the next blank line.
				******************************************************************************/
				
				do
        			if(fgets((char *) Inst,MAXLENGTH,input_relators) == NULL) return(3);
    			while(*Inst != '\n' && *Inst != '\r');
    			
    			/******** Found a blank line. Go to the beginning. ***********/
    			
				goto TOP;
				}            
            p++;        
            }                                
  		if(*Inst== '\n') break;
        StrLength = strlen((char *) Inst);
        if(StrLength >= MAXLENGTH) return(4);
        if(StrLength == h) break;
        NumRelators ++;
        if(NumRelators == 1 && Flag)
        	{
    		printf("\n\n------------------------------------");        	
        	printf("\n\n%s",PresName);
        	}
        if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
        Relators[i] = (unsigned char **) NewHandle(StrLength + 1 - h);
        if(Relators[i] == NULL) Mem_Error();
        LR[i] = StrLength - h;
        p = *Relators[i];    
  		q = Inst + h;		
        while( (*p++ = *q++) ) ;         
        if(fgets((char *) Inst,MAXLENGTH,input_relators) == NULL) break;         
        }
    if(NumRelators == MAXNUMRELATORS) return(5);
    
    if(Flag) Print_Relators(Relators, NumRelators);
    
    return(0);
}

int Is_IP_In_HS_Reps(int NumHSReps,int* HSRepL)
{
	unsigned char   Match,
					*p,
                    *q;
    
    unsigned int    i,
    				j,
                    k,
                    l,
                    m; 
    
    /******************************************************************************************
    				  See if the IP appears in the list of HS Reps.
    ******************************************************************************************/
    
    CheckHSReps = FALSE;
    
 	for(i = j = 0,Match = FALSE; i < NumHSReps; i++)
		{		
		if(HSRepL[i] < 0) 
			{
			k = 1;
			j++;
			continue;
			}
		if(HSRepL[i] >= INFINITE)
			{
			/* The canonical rep presentation is new. */
			l = HSRepL[i] - INFINITE;
			ReadPres = SUR_Num[l];
			if(CopyNumRelators != NR[ReadPres]) continue;						
			for(m = 1; m <= NumRelators; m++)
				{
				p = *SMGP[l][m];
				q = *Copy_Of_Input[m];
				while(*p && (*q++ == *p++) ) ;
				if((*p == EOS) && (*q == EOS)) continue;
				break;
				}
			if(m > NumRelators)	
				{
				Match = TRUE;
				break;
				}
			k++;		
			}
		else 
			{
			ReadPres = HSRepL[i];
			if(CopyNumRelators != NR[ReadPres]) continue;			
			for(m = 1; m <= NumRelators; m++)
				{
				p = *SUR[ReadPres][m];
				q = *Copy_Of_Input[m];
				while(*p && (*q++ == *p++) ) ;
				if((*p == EOS) && (*q == EOS)) continue;
				break;
				}
			if(m > NumRelators)	
				{
				Match = TRUE;
				break;
				}	
			k++;
			}
		}
		
	for(i = m = 0; i < NumHSReps; i++) if(HSRepL[i] > 0) m++;
		
	if(Match) printf("\n\nThe IP appears in the HS_Rep List of %u HS Reps as HS %d, P %d.",m,j,k);
	else printf("\n\n%s <-- Not a HS Rep!",PresName);
	if(Batch == 53 && H_Results != NULL) 
		{
		if(Match) fprintf(H_Results,"\n\n%s appears as HS %d, P %d of %u HS Reps",PresName,j,k,m);
		else fprintf(H_Results,"\n\n%s <-- Not a HS Rep!",PresName);
		}
	return(0);
}

int Search_For_Non_Minimal_UnStabilized_Splittings(char F1,int TargetNumGenerators)
{
	FILE			*fptr1,
					*fptr2;
					
	int				i,
					j,
					MyMinNumGenerators;
	
	if(F1) Check_for_1_HS  = TRUE;
	else   Check_for_1_HS2 = TRUE;
	
	if(F1) while(NumGenerators < TargetNumGenerators && Stabilize(FALSE) == 0) ;
		
	Just_Delete_Primitives(FALSE,3);

	/************************************************************
		Find the minimal number of generators occurring in the 
		presentations Just_Delete_Primitives(FALSE,3) found. 
	************************************************************/

	for(i = 0, MyMinNumGenerators = 10000; i < NumFilled; i++) 
		if(NG[i] < MyMinNumGenerators) MyMinNumGenerators = NG[i];

	if(MyMinNumGenerators < 2) 
		{
		printf("\n\nA splitting has at most one generator!");
		return(1);
		}

	MyMinNumGenerators ++;	

	/******************************************************************************************** 
		Stash the presentations Just_Delete_Primitives(FALSE,TRUE) found on MyMinNumGenerators 
		in the file 'Heegaard_Input_Pres2'. Then erase the current set of presentations and 
		reload the presentations stashed in 'Heegaard_Input_Pres2' into memory. 
	********************************************************************************************/

    fptr1 = input_relators;
    fptr2 = fopen("Heegaard_Input_Pres2","w+");  
	if(fptr2 == NULL)
        {
        printf("\n\nUnable to open the file 'Heegaard_Input_Pres2'.");
        return(-1);
        }    
    input_relators = fptr2;          
        
    for(i = j = 0; i < NumFilled; i++) if(NG[i] == MyMinNumGenerators)
    	{
    	fprintf(input_relators,"\n\nP %d) Gen %d, Rel %d, L %lu",i+1,NG[i],NR[i],SURL[i]);
    	Print_Relators3(SUR[i],NR[i]);
    	j++;
    	}
    if(j == 0) 
    	{
 		input_relators = fptr1;
		fclose(fptr2);   	
    	return(-1);
    	}
    
    fseek(input_relators,0L,0);
    Delete_Old_Presentations();    	
	Init_G_Variables();
	if(F1) Check_for_1_HS  = TRUE;
	else   Check_for_1_HS2 = TRUE;
	NumGenerators = MyMinNumGenerators;
	
	while(1) 
		{
		if(Get_Next_Presentation_From_File(FALSE)) break;
		for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
		Length -= NumRelators;
		Save_Pres(0,0,Length,1,0,0,0,0);
		}
		
	if(NumFilled == 0)
		{
 		input_relators = fptr1;
		fclose(fptr2);   	
    	return(-1);		
		}	
		
	for(i = 0; i < NumFilled; i++)
		{
		HegSplNum[i] = i;
		HegSplNxt[i] = i;
		SURNumX[i]   = 1;
		NumLoops[i]  = 0;
		QPM[i] 		 = 0;
		UDV[i]		 = 0;
		}
	
	Batch							= FALSE;			
	BreadthFirstSearch 				= TRUE;
	DepthFirstSearch 				= FALSE;
	Input 							= RESET;
	Check_If_HS_Rep					= FALSE;	
	Delete_Only_Short_Primitives 	= FALSE;	
	Do_Not_Reduce_Genus 			= TRUE;
	Find_All_Min_Pres 				= FALSE;
	FormBandsums 					= TRUE;
	OnlyReducingBandsums 			= FALSE;
	
	Mergers = 0;
	MyMaxSavedPres4 = MyMaxSavedPres3 + NumFilled;
	
	printf("\n\nLooking for HS Reps of %u genus %d presentations. Hit 's' for status reports. Hit ' ' for a chance to abort.",NumFilled, NumGenerators);
	
	switch(Get_Diagrams())
		{
		case ONE_HS_REP:
			input_relators = fptr1;
			fclose(fptr2);		
			return(1);
		case INTERRUPT:
			break;
		case QUIT_FLAG:
			{
			input_relators = fptr1;
			fclose(fptr2);
			return(QUIT_FLAG);			
			}				
		default:
			printf("\n\nNumFilled %u, Diagrams %ld.",NumFilled,NumDiagrams);
			if(!F1 && NumFilled >= MyMaxSavedPres4) printf("\n\nNumFilled %u >= MyMaxSavedPres4 %u.",NumFilled, MyMaxSavedPres4);
			if(!F1 && NumDiagrams >= MyMaxNumDiagrams3) printf("\n\nNumDiagrams %ld >= MyMaxNumDiagrams3 %ld.",NumDiagrams, MyMaxNumDiagrams3);
			break;	
		}

	if(TotalComp > 1)
		{
		printf("\n\nMore than one component!");
		input_relators = fptr1;
		fclose(fptr2);		
		return(-1);
		}
					
	for(i = 0; i < NumFilled; i++) Table1[i] = i;
    
    qksort1(NumFilled);

	LastPresRead = NumFilled - 1;				
	j = Init_Find_Canonical_Orbit_Reps(Table1,LastPresRead,1);		
	if(j >= 0 && j < TOO_LONG) switch(Find_Canonical_Orbit_Reps(Table1,j,1,1,FALSE,0)) 
		{
		case 0:
			break;
		case QUIT_FLAG:
			input_relators = fptr1;
			fclose(fptr2);
			return(QUIT_FLAG);
		case TOO_LONG:
			printf("\n\nFind_Canonical_Orbit_Reps() returned TOO_LONG.");
			NumSplittings = -1;
			break;	
		}

	input_relators = fptr1;
	fclose(fptr2);		
						
	return(NumSplittings);
}

int Check_HS_Reducibility(int NumHSReps,int* HSRepL,char* HSL2)
{
	unsigned char	*p,
					*q,
					Reducible;
				
	int				CPRV,
					i,
					j,
					k,
					l,
					m,
					NumPresChecked = 0,
					NumReducible,
					SNumGenerators,
					SNumRelators;
				
	/*************************************************************************************************
		This routine runs a simple check for possible Reducibile Heegaard splittings. For each 
		splitting, it checks whether there is a relator of an HS_Rep which is primitive or a 
		proper-power. 
	*************************************************************************************************/

	for(i = 0,Reducible = FALSE,NumReducible = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{			
			j = -HSRepL[i];
			k = 1;
			Reducible = FALSE;
			continue;
			}
		if(HSL2[j]) continue;			
		if(Reducible) continue;
		if(NumReducible == 0) NumReducible = 1;
		NumPresChecked ++;
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new. */
			l 				= HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = SNumRelators; m > 0; m--)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumGenerators 	= SNumGenerators;
				NumRelators 	= 1;
				Vertices 		= 2*NumGenerators;
				CPRV = CheckPrimitivity();
				if(CPRV == -1 && SNumGenerators > 1)
					{
					printf("\nHS %d is Reducible: Relator %d of P %d is a proper-power!",j,m,k);
					Reducible = TRUE;
					HSL2[j] = 1;							
					}
				if(CPRV == 1)
					{
					printf("\nHS %d is Reducible: Relator %d of P %d is primitive!",j,m,k);
					Reducible = TRUE;
					NumReducible ++;
					HSL2[j] = 1;
					}
				if(Reducible) break;							
				}	
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = SNumRelators; m > 0; m--)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumGenerators 	= SNumGenerators;
				NumRelators 	= 1;
				Vertices 		= 2*NumGenerators;
				CPRV = CheckPrimitivity();
				if(CPRV == -1 && NumGenerators > 1)
					{
					printf("\nHS %d is Reducible: Relator %d of P %d is a proper-power!",j,m,k);
					Reducible = TRUE;
					HSL2[j] = 1;							
					}
				if(CPRV == 1)
					{
					printf("\nHS %d is Reducible: Relator %d of P %d is primitive!",j,m,k);
					Reducible = TRUE;
					NumReducible ++;
					HSL2[j] = 1;
					}
				if(Reducible) break;	
				}	
			k++;
			}	
		}
	
	if(NumReducible == 1) printf("\nChecked each relator of %d HS Rep(s). Found no primitive or proper-power relators.",NumPresChecked);	
	return(0);	
}

int Check_HS_Weak_Reducibility(int NumHSReps,int* HSRepL,char* HSL2)
{
	unsigned char	*p,
					*q,
					WeaklyReducible;
				
	int				i,
					ii,
					j,
					jj,
					k,
					kk,
					l,
					m,
					NumPresChecked = 0,
					NumWeaklyReducible,
					SNumGenerators,
					SNumRelators;
					
	unsigned int	C[125];				
				
	/*************************************************************************************************
		This routine runs a simple check for possible Weakly Reducibile Heegaard splittings. For 
		each HS splitting, it checks whether there is a relator, say R, of an HS_Rep with the 
		property that R has less than full-rank in the underlying handlebody H. I.e. R is disjoint 
		from some meridional disk of H. In this case, the HS has the 'disjoint disk property' and 
		is a distance <= 1 splitting. 
	*************************************************************************************************/

	for(i = 0,WeaklyReducible = TRUE,NumWeaklyReducible = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{			
			j = -HSRepL[i];
			k = 1;
			WeaklyReducible = FALSE;
			continue;
			}
		if(HSL2[j]) continue;	
		if(WeaklyReducible) continue;
		if(NumWeaklyReducible == 0) NumWeaklyReducible = 1;
		NumPresChecked ++;
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new. */
			l 				= HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = 1; m <= SNumRelators; m++)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumGenerators 	= SNumGenerators;
				NumRelators 	= 1;
				Vertices 		= 2*NumGenerators;
				if(CheckPrimitivity() == 0)
					{
					/**************************************************
						Check if Relators[1] has less than full-rank.
					***************************************************/	
					for(ii = 0; ii < SNumGenerators; ii++) C[ii+'A'] = C[ii+'a'] = 0;
					p = *Relators[1];
					while(*p)
						C[*p++]++;
					for(ii = jj = kk = 0; ii < SNumGenerators; ii++,jj+=2)
						{
						C[ii+'A'] += C[ii+'a'];
						C[jj] = C[ii+'A'];
						if(C[jj]) kk++;
						}
					if(kk < SNumGenerators) /* Relators[1] has less than full-rank. */
						{
						printf("\nHS %d is Weakly Reducible: Relator %d of P %d has less than full-rank.",j,m,k);
						WeaklyReducible = TRUE;
						NumWeaklyReducible ++;
						HSL2[j] = 2;							
						}
					}
				if(WeaklyReducible) break;	
				}	
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = 1; m <= SNumRelators; m++)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumGenerators 	= SNumGenerators;
				NumRelators 	= 1;
				Vertices 		= 2*NumGenerators;
				if(CheckPrimitivity() == 0)
					{
					/**************************************************
						Check if Relators[1] has less than full-rank.
					***************************************************/	
					for(ii = 0; ii < SNumGenerators; ii++) C[ii+'A'] = C[ii+'a'] = 0;
					p = *Relators[1];
					while(*p)
						C[*p++]++;
					for(ii = jj = kk = 0; ii < SNumGenerators; ii++,jj+=2)
						{
						C[ii+'A'] += C[ii+'a'];
						C[jj] = C[ii+'A'];
						if(C[jj]) kk++;
						}
					if(kk < SNumGenerators) /* Relators[1] has less than full-rank. */
						{
						printf("\nHS %d is Weakly Reducible: Relator %d of P %d has less than full-rank.",j,m,k);
						WeaklyReducible = TRUE;
						NumWeaklyReducible ++;
						HSL2[j] = 2;						
						}
					}
				if(WeaklyReducible) break;	
				}	
			k++;
			}	
		}
	if(NumWeaklyReducible == 1) printf("\nChecked each relator of %d HS Rep(s). Each checked relator has full-rank.",NumPresChecked);	
	
	return(0);	
}

int Check_HS_Disjoint_Curves(int NumHSReps,int* HSRepL,char* HSL2)
{
	unsigned char	DisjointCurve,
					*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m,
					NumDisjointCurve,
					NumPresChecked = 0,
					SNumGenerators,
					SNumRelators;									
				
	/*************************************************************************************************
		This routine runs a simple check for disjoint curves in splittings. For each HS splitting 
		in which each relator of each HS_Rep has full-rank, the routine checks whether there is a 
		relator R of an HS_Rep with the property that R is disjoint from a simple-circuit C 
		which has less than full-rank in the underlying handlebody H. If such a curve C exists, the 
		splitting has the 'disjoint curve property' and has distance <= 2.
	*************************************************************************************************/

	for(i = 0,DisjointCurve = TRUE,NumDisjointCurve = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{			
			j = -HSRepL[i];
			k = 1;
			DisjointCurve = FALSE;
			continue;
			}
		if(HSL2[j]) continue;	
		if(DisjointCurve) continue;	
		if(NumDisjointCurve == 0) NumDisjointCurve = 1;
		NumPresChecked ++;
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new. */
			l 				= HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = 1; m <= SNumRelators; m++)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				NumGenerators   = SNumGenerators;
				NumRelators		= 1;
				Vertices 		= 2*SNumGenerators;								
				Length 			= GetHandleSize((char **) Relators[1]) - 1;
				/*****************************************************************************************
					First, try to get a diagram for Relators[1]. Then call Find_Simple_Circuits() to see
					if there is a simple-circuit C with less than full-rank disjoint from Relators[1].
				******************************************************************************************/					
				if(Get_Relators1_Diagram()) continue;
				if(Find_Simple_Circuits())
					{
					printf("\nHS %d has disjoint curves: There is a simple-circuit with less than full-rank disjoint from Relator %d of P %d.",j,m,k);					
					DisjointCurve = TRUE;
					NumDisjointCurve ++;
					HSL2[j] = 4;
					}
				if(DisjointCurve) break;	
				}	
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			SNumGenerators 	= NG[ReadPres];
			SNumRelators 	= NR[ReadPres];
			for(m = 1; m <= SNumRelators; m++)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[1] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[1];
				while( (*q++ = *p++) ) ;
				NumGenerators   = SNumGenerators;
				NumRelators		= 1;
				Vertices 		= 2*SNumGenerators;								
				Length 			= GetHandleSize((char **) Relators[1]) - 1;
				/*****************************************************************************************
					First, try to get a diagram for Relators[1]. Then call Find_Simple_Circuits() to see
					if there is a simple-circuit C with less than full-rank disjoint from Relators[1].
				******************************************************************************************/
				if(Get_Relators1_Diagram()) continue;
				if(Find_Simple_Circuits())
					{
					printf("\nHS %d has disjoint curves: There is a simple-circuit with less than full-rank disjoint from Relator %d of P %d.",j,m,k);					
					DisjointCurve = TRUE;
					NumDisjointCurve ++;
					HSL2[j] = 4;
					}
				if(DisjointCurve) break;	
				}	
			k++;
			}	
		}
	
	if(NumDisjointCurve == 1) printf("\nChecked %d HS Rep(s). No disjoint curves found.",NumPresChecked);	
	return(0);	
}

int Get_Relators1_Diagram(void)
{
	int				LTRV,
					WGRV;
	
	unsigned int	i,
					j;
					
	/********************************************************************************************
						Try to find a realizable diagram of Relators[1].
	********************************************************************************************/
	
_GET_DIAGRAM:
    
    Saved_Vertices = 0;
    TestRealizability1 = TRUE;
    Fill_A(NumRelators);
    if(Find_Flow_A(NORMAL,FALSE)) return(2);
    WGRV = Whitehead_Graph();  
    switch(WGRV)
        {
        case NO_ERROR:
            break;
        case NON_PLANAR:
        case FATAL_ERROR:
        case TOO_LONG:
        case TOO_MANY_COMPONENTS:        
        case NON_UNIQUE_1:
        case NON_UNIQUE_2:
        case NON_UNIQUE_3:
        case NON_UNIQUE_4:
        case V2_ANNULUS_EXISTS:    
        case NOT_CONNECTED:
            TestRealizability1 = FALSE;
            if(Micro_Print == 1)
            	{
            	printf("\n\nWhitehead_Graph() returned an error. Cause:");
            	Micro_Print_Whitehead_Graph_Return_Value(WGRV);
            	}
            return(2);
        case SEP_PAIRS:
            Num_Saved_LPres = 0;
            NotNewPres = 0;
            LTRV = Level_Transformations(FALSE,TRUE,TRUE);
 	        for(i = 0; i < Num_Saved_LPres; i++)
            for(j = 1; j <= NumRelators; j++) if(SLR[i][j] != NULL)
            	{
            	DisposeHandle((char **) SLR[i][j]);
            	SLR[i][j] = NULL;
            	}
            switch(LTRV)
                {
                case 0:
                case 1:
                	TestRealizability1 = FALSE;	
                    return(2);
                case 2: 
                	{
                	if(Micro_Print == 1)
                		printf("\n\nPerformed some level-transformations on the input presentation.");	   
                	goto _GET_DIAGRAM;
                	}
                default:
                	TestRealizability1 = FALSE;				
                    return(2);
                }    
        default:
        	TestRealizability1 = FALSE;
            if(Micro_Print == 1)
            	{
            	printf("\n\nWhitehead_Graph() returned an error. Cause:");
            	Micro_Print_Whitehead_Graph_Return_Value(WGRV);
            	}        	
            return(2);
        }
    
    TestRealizability1 = FALSE; 
	
	return(0);
}

int Check_HS_Strong_Irreducibility(int NumHSReps,int* HSRepL,char* HSL2)
{
	unsigned char	FoundSIrreducible,
					*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m,
					RV,
					NumPresChecked = 0,
					NumSIrreducible;
								
	for(i = NumSIrreducible = 0,FoundSIrreducible = FALSE; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{
			j = -HSRepL[i];
			k = 1;
			FoundSIrreducible = FALSE;
			continue;
			}
		if(HSL2[j] == 1 || HSL2[j] == 2) continue;
		if(FoundSIrreducible) continue;
		if(NumSIrreducible == 0) NumSIrreducible = 1;
		NumPresChecked ++;
		if(HSRepL[i] >= INFINITE) 
			{
			/* The canonical rep presentation is new. */
			l 				= HSRepL[i] - INFINITE;
			ReadPres 		= SUR_Num[l];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[l][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SMGP[l][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
			
			RV = Check_HS_Strong_IrreducibilityS1();
			if(RV == TOO_LONG) printf("\nCould not find a diagram for P %d of HS %d.",k,j);	
			if(RV == 0) 
				{
				FoundSIrreducible = TRUE;
				NumSIrreducible++;
				printf("\nHS %d is Strongly Irreducible: The diagram of P %d of HS %d has no 'disjoint-waves'.",j,k,j);
				if(HSL2[j] == 0) HSL2[j] = 5;
				}
			if(RV == 1 && Micro_Print == 5) printf(" in the diagram of P %d of HS %d.",k,j);	
			k++;		
			}
		else 
			{
			ReadPres 		= HSRepL[i];
			NumGenerators 	= NG[ReadPres];
			NumRelators 	= NR[ReadPres];
			Length 			= SURL[ReadPres];
			Vertices 		= 2*NumGenerators;
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}
			
			RV = Check_HS_Strong_IrreducibilityS1();
			if(RV == TOO_LONG) printf("\nCould not find a diagram for P %d of HS %d.",k,j);	
			if(RV == 0) 
				{
				FoundSIrreducible = TRUE;
				NumSIrreducible++;
				printf("\nHS %d is Strongly Irreducible: The diagram of P %d of HS %d has no 'disjoint-waves'.",j,k,j);
				if(HSL2[j] == 0) HSL2[j] = 5;
				}
			if(RV == 1 && Micro_Print == 5) printf(" in the diagram of P %d of HS %d.",k,j);	
			k++;
			}
		}
		
	if(NumSIrreducible == 1) printf("\nChecked diagrams of %d HS Rep(s): All could have 'disjoint-waves'.",NumPresChecked);

	return(0);		
}

int Check_HS_Strong_IrreducibilityS1(void)
{
	/********************************************************************************************
		Check_HS_Strong_IrreducibilityS1() looks for possible minimal 'disjoint-waves' and 
		checks whether each 'disjoint-wave' candidate has a Whitehead graph which is connected 
		and has no cut-vertex. If the graph of each minimal 'disjoint-wave' candidate is 
		connected and does not have a cut-vertex, the HS is Strongly Irreducible.
		 	Choosing option 'X' sets Micro_Print = 6 which prints the output listed below. 
		In particular, when Micro_Print = 6, Heegaard prints all 'disjoint-wave' candidates 
		and 'disjoint-loop' candidates which traverse a face at most once, except for loops 
		where the initial and terminal face are identical.
			When Micro_Wave == 7, Heegaard prints all of the minimal 'disjoint-wave'
		candidates which it finds.
			(Ideally, when a manifold has boundary, candidate 'disjoint-waves', which do not
		cut off a planar surface whose boundary bnds a disk, should be filtered out, but this
		has not been implemented.)		
	********************************************************************************************/							
							
	unsigned char 	*BadPath = NULL,
					**BdryRelsFace = NULL,
					*FacesVisited = NULL,
					*FacesVisitedList = NULL,
					FoundPossibleWave,
					InitialFace,
					NumPathsInWave,
					*p,
					*Pl = NULL,
					**PM = NULL,
					*PM_From = NULL,
					*PM_To = NULL,
					**PP = NULL,
					*PP_From = NULL,
					*PP_To = NULL,
					*Pr = NULL,
					PossibleNewTerminalFace,
					*q,
					*r,
					*SRelator1 = NULL,
					TerminalFace,
					*T2 = NULL,
					tl,
					tr,
					V1,
					V2,
					V3,
					V4,
					x;
													
	int 			Big_Number = 50000,
					Error,
					FoundWave,
					ii,
					jj,
					kk,
					*PathsInWave = NULL,
					**P_From_Face = NULL,
					*pp,
					ss,
					SNumGenerators,
					SNumRelators;
							
	unsigned int 	c,
					d,
					e,
					edge,
					EL[6*VERTICES],
					ee,
					h,
					i,
					j,
					k,
					NumPaths,
					NumPossibleWavesFound,
					v,
					vertex,
					vertexRS,
					vertexLE,
					w;
	
	long 			HSS = 0,
					length;
	
	unsigned long	max;
	
	if(NumRelators <= 1) return(FALSE);
	
	Error = 0;
	NumPaths = 0;
	
	Fill_A(NumRelators);				
	if(ComputeValences_A()) return(TOO_LONG);
	Get_Matrix();
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;
	if(Connected_(0,0) == FALSE) return(TOO_LONG);
	Num_Saved_LPres = 0;
	if(Sep_Pairs(0,0,1))
		{
		if(Level_Transformations(FALSE,FALSE,TRUE) != 2)
			{		
			printf("\nCould not remove all separating pairs of vertices.");
			return(TOO_LONG);		
			}
		if(Num_Saved_LPres > 0) printf("\nPerformed some level-transformations on the input presentation.");	
		Fill_A(NumRelators);				
		if(ComputeValences_A()) return(TOO_LONG);
		Get_Matrix();
		}
	if(Planar(FALSE,TRUE) == TRUE) return(TOO_LONG);
	if(Diagram_Main()) return(TOO_LONG);

	BdryRelsFace = (unsigned char **) NewPtr(sizeof(long)*(NumFaces + 1));
	if(BdryRelsFace == NULL) Mem_Error();
	Pl = (unsigned char*) NewPtr(sizeof(char)*(NumEdges + 1));
	if(Pl == NULL) Mem_Error();
	PM = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PM == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PM[d] = NULL;	
	PP = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PP == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PP[d] = NULL;
	P_From_Face = (int **) NewPtr(sizeof(long)*(NumFaces + 1));
	if(P_From_Face == NULL) Mem_Error();
	for(d = 1; d <= NumFaces; d++) P_From_Face[d] = NULL;	
	PM_From = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PM_From == NULL) Mem_Error();
	PP_From = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_From == NULL) Mem_Error();
	PM_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PM_To == NULL) Mem_Error();
	PP_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_To == NULL) Mem_Error();
	Pr = (unsigned char*) NewPtr(sizeof(char)*(NumEdges + 1));
	if(Pr == NULL) Mem_Error();	
	PathsInWave = (int *) NewPtr(sizeof(int)*(NumFaces + 2));
	if(PathsInWave == NULL) Mem_Error();
	FacesVisitedList = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 2));
	if(FacesVisitedList == NULL) Mem_Error();
	FacesVisited = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 1));
	if(FacesVisited == NULL) Mem_Error();

	for(d = 1,max = 0L; d <= NumRelators; d++) if(LR[d] > max) max = LR[d];
	T2 = (unsigned char *) NewPtr(max + 2);
	if(T2 == NULL) Mem_Error();	
	for(d = 1; d <= 2*NumEdges; d++) EL[d] = d;
	NumPaths = 0;
	printf("\n");
	if(Micro_Print == 6) printf("\nListing all 'disjoint-wave' and 'disjoint-loop' candidates which traverse a face at most once.");				
	for(ss = 2*NumEdges; ss > 0; ss --)
		{		
		/**************************************************************************************
			Determine which edges of the original diagram are joined by the edge ss of the dual
			diagram.
		**************************************************************************************/	
		
		for(v = c = 0; c + VWG[v] < EL[ss]; v++) c += VWG[v];
		w = EL[ss] - c;
		for(c = ee = 0,vertexLE = d = FV[v]; c < w; c++)
			{
			ee += A[v][d];
			vertexLE = d;
			d = CO[v][d];
			}
		e = ee - 1;
		if(v & 1)
			{	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			if(e) e--;
			else e = V[v] - 1;
			}
		
		p = q = *DualRelators[(v >> 1) + 1] + e;
		q++;
		if(!*q) q = *DualRelators[(v >> 1) + 1];
		if(v & 1)
			{
			tr = *p;
			tl = *q;
			if(tr > 95) tr -= 32;
			else tr += 32;
			}
		else
			{
			tl = *p;
			tr = *q;
			if(tl > 95) tl -= 32;
			else tl += 32;
			}	
		
		length	= 0L;
		vertex  = v;
		V2 		= vertex;
		edge    = ee % V[v];
		e 		= edge;
		r		= T2;
		
		/**************************************************************************************
			Two relators have come from distinct vertices and are adjacent to each other at
			vertex v. Follow these two relators along until they diverge. The region where
			they are parallel is the "cancellation region".
		**************************************************************************************/	
		
		do
			{
			if(v & 1)
				{
				*r = (v >> 1) + 97;
				w = v - 1;
				}
			else
				{
				*r = (v >> 1) + 65;
				w = v + 1;
				}
			V4 = v;	
			r++;	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			length ++;
			if(length > max)
				{			
				Error = 2;
				goto END;
				}	
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}	
			if(e == (d - 1))	
				{
				/***********************************************************************
					If e = d - 1, then we have found the end of the cancellation region.
				***********************************************************************/
				
				*r++ = EOS;
				if(V4 & 1)
					V4 -= 1;
				else
					V4 += 1;
				vertexRS = v;
				
				/***********************************************************************
					Determine which edge of the dual diagram corresponds to the end of
					the cancellation region and delete it from the list of available
					edges.
				***********************************************************************/	
				
				for(d = 0,c = 1; d < w; d++) c += VWG[d];
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					c++;
					v = CO[w][v];
					d += A[w][v];
					}
				if(EL[c] == c)
					{
					ss --;
					v = EL[ss];
					EL[ss] = c;
					EL[c] = v;
					}	
				else
					{
					for(d = 1; d < ss && (EL[d] != c); d++) ;
					if(d < ss)
						{
						ss --;
						v = EL[ss];
						EL[ss] = c;
						EL[d] = v;
						}
					}
				if(vertexLE & 1)
					x = (vertexLE >> 1) + 97;
				else
					x = (vertexLE >> 1) + 65;
				V1 = vertexLE;
				V3 = vertexRS;
				
				HSS = r - T2;
				NumPaths ++;
				
				PP[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PP[NumPaths] == NULL) Mem_Error();
				q = PP[NumPaths];	
				p = T2;
				while( (*q++ = *p++) ) ;

				PM[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PM[NumPaths] == NULL) Mem_Error();
				Inverse(PP[NumPaths]);
				q = PM[NumPaths];	
				p = PP[NumPaths];
				while( (*q++ = *p++) ) ;
				Inverse(PP[NumPaths]);
							
				/***********************************************************************************
							Identify the initial and terminal faces of this path.
				***********************************************************************************/
				
				for(h = 1,i = FALSE; h <= NumFaces; h++)
					{
					p = Face[h];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V1)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[h];
							if(*q == V2)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}
					
				for(j = 1,i = FALSE; j <= NumFaces; j++)
					{
					p = Face[j];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V3)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[j];
							if(*q == V4)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}

				PP_From[NumPaths] = h;
				PP_To[NumPaths]   = j;
				PM_From[NumPaths] = j;
				PM_To[NumPaths]   = h;
				Pl[NumPaths] = tl;
				Pr[NumPaths] = tr;
				if(Micro_Print == 6) printf("\nP%2u) %c|%c, F%2u --> F%2u: %s",NumPaths,tl,tr,h,j,PP[NumPaths]);	
				break;				
				}
				
			e = B[w][v] - e;
			}	
		while(v != vertex || e != edge);	
	}
	
	DisposePtr((char *) T2);

	for(i = 1; i <= NumFaces; i++)
		{
		p = Face[i];
		j = 2;
		while(*p++ < VERTICES) j++;
		P_From_Face[i] = (int *)NewPtr(sizeof(int)*j);
		if(P_From_Face[i] == NULL) Mem_Error();
		P_From_Face[i][0] = 1;
		P_From_Face[i][j-1] = Big_Number;
		for(h = 1; h < j-1; h++) P_From_Face[i][h] = 0;
		BdryRelsFace[i] = (unsigned char *)NewPtr(sizeof(char)*(2*j-3));
		if(BdryRelsFace[i] == NULL) Mem_Error();
		}	
		
	for(ii = 1; ii <= NumPaths; ii++)
		{
		pp = P_From_Face[PP_From[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = ii;
		pp = P_From_Face[PP_To[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = -ii;	
		}
		

	if(Micro_Print == 6) for(i = 1; i <= NumFaces; i++)
		{
		pp = P_From_Face[i];
		printf("\nPaths from F%2d: ",i);
		pp ++;
		while(*pp != Big_Number) 
			{
			printf("%d ",*pp);
			pp++;
			}
		}
				
	for(i = 1; i <= NumFaces; i++)
		{
		pp = P_From_Face[i];
		pp ++;
		q = BdryRelsFace[i];
		while(*pp != Big_Number)
			{
			ii = *pp;
			tl = Pl[abs(ii)];
			tr = Pr[abs(ii)];
			*q++ = tl;
			*q++ = tr;				
			pp++;
			}
		*q = EOS;	
		}
		
	if(Micro_Print == 6) for(i = 1; i <= NumFaces; i++) printf("\nFace[%d]BdryRels %s",i,BdryRelsFace[i]); 
	if(Micro_Print == 7) printf("\nListing all minimal 'disjoint-wave' candidates.");
		
	/* Check for possible waves to relators that lie completely in a face. */
	
	for(i = 1; i <= NumFaces; i++)
		{
		p = BdryRelsFace[i];
		while(*p)
			{
			j = 0;
			q = p;
			while(*q++) if(*q == *p) j++;
			if(j > 2)
				{
				printf("\nThere is a possible wave in face %d.",i);
				printf(" A char appears more than twice in BdryRelsFace[%d] = %s.",i,BdryRelsFace[i]);
				if(Micro_Print != 6) break;
				}
			p++;
			}	
		if(j > 2) break;
		}

	/* Save copies of Relators[1], NumGenerators, and NumRelators. */
	
	SNumGenerators = NumGenerators;
	SNumRelators   = NumRelators;
	
	if(Relators[1] != NULL)
		{
		SRelator1 = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[1]));
		if(SRelator1 == NULL) Mem_Error();		
		p = *Relators[1];
		q = SRelator1;
		while((*q++ = *p++)) ;	
		}
		
	/* Check each path for cut-vertices. */
	
	BadPath = (unsigned char*) NewPtr(sizeof(char)*(NumPaths + 1));
	if(BadPath == NULL) Mem_Error();
		
	for(i = 1,j = 0; i <= NumPaths; i++)
		{
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetPtrSize(PP[i]));
		if(Relators[1] == NULL) Mem_Error();
		q = *Relators[1];
		p = PP[i];
		while( (*q++ = *p++) ) ;
		if(CP_Find_Primitives(FALSE)) BadPath[i] = 1;
		else 
			{
			BadPath[i] = FALSE;
			j++;
			}
		if(Micro_Print == 6) printf("\nPath[%d] %s, BadPath[%d] = %d",i,PP[i],i,BadPath[i]);
		}
		
	if(Micro_Print == 6) printf("\nNumPaths %d, NumGoodPaths %d",NumPaths,j);

	for(i = 1,NumPossibleWavesFound = 0,FoundWave = FALSE; i <= NumFaces; i++)
		{
		InitialFace = i;
		TerminalFace = i;
		NumPathsInWave = 0;
		for(j = 1; j <= NumFaces; j++) FacesVisited[j] = FALSE; 
		FacesVisited[InitialFace] = TRUE;
		FacesVisitedList[1] = InitialFace;
		while(1)
			{
			h = P_From_Face[TerminalFace][0];
			P_From_Face[TerminalFace][0] ++;
			ii = P_From_Face[TerminalFace][h];
			if(ii != Big_Number && BadPath[abs(ii)] == 0) continue;	
			if(ii == Big_Number)
				{
				/*  We've reached a dead end. No new path from the current terminal face leads to a new face.
					Clear info for the current terminal face and reset the terminal face to the previous face. 	*/ 

				P_From_Face[TerminalFace][0] = 1;
				FacesVisited[TerminalFace] = FALSE;
				if(NumPathsInWave == 0) break; 
				NumPathsInWave --;
				TerminalFace = FacesVisitedList[NumPathsInWave + 1];		
				continue;
				}
			if(ii != Big_Number)
				{
				FoundPossibleWave = FALSE;
				if(ii > 0) PossibleNewTerminalFace = PP_To[ii];
				if(ii < 0) PossibleNewTerminalFace = PM_To[-ii];
				if(PossibleNewTerminalFace == InitialFace)
					{
					if((NumPathsInWave == 0) && (ii < 0)) continue;
					if((NumPathsInWave > 0) && (ii == -PathsInWave[1])) continue;
					if((NumPathsInWave > 0) && (abs(ii) < abs(PathsInWave[1]))) continue;
					NumPathsInWave ++;														
					PathsInWave[NumPathsInWave] = ii;

					/************************************************************************************
						A simple closed curve C in the Heegaard surface disjoint from the relators and
						a disk in H, must contain a 'loop' with both ends in the same face. If the 
						Whitehead graph of the 'loop' is connected and has no cut-vertex, it can't be 
						extended to a simple closed curve C disjoint from the relators and a disk in H. 	
					************************************************************************************/
					
					kk = Check_HS_Strong_IrreducibilityS2(NumPathsInWave,PathsInWave,PP,PM);
					if(kk && kk != TOO_LONG)
						{
						NumPossibleWavesFound ++;
						if(Micro_Print == 5 || Micro_Print == 6)
							{
							printf("\n%u) Found a possible 'disjoint-loop': %s \n",NumPossibleWavesFound,(char *) *Relators[1]);
							printf("with Faces and Paths: ");
							for(j = 1; j <= NumPathsInWave; j++) 
								printf("F%d,P%d,",FacesVisitedList[j],PathsInWave[j]);
								printf("F%d",PossibleNewTerminalFace);
							}		
						FoundWave = TRUE;	
						if(Micro_Print != 6) goto FOUND_WAVE;
						}					
					if(kk == TOO_LONG) goto FOUND_WAVE;
					NumPathsInWave --;
					continue;	
					}				
				if(FacesVisited[PossibleNewTerminalFace] == FALSE)
					{
					TerminalFace = PossibleNewTerminalFace;
					NumPathsInWave ++;
					PathsInWave[NumPathsInWave] = ii;
					FacesVisited[TerminalFace] = TRUE;
					FacesVisitedList[NumPathsInWave + 1] = TerminalFace;
					FoundPossibleWave = TRUE;
					
					/* Check if the graph of the current PATH is connected and has no cut-vertex. */
					
					kk = Check_HS_Strong_IrreducibilityS2(NumPathsInWave,PathsInWave,PP,PM);		

					if(kk == 0) 
						{
						/*********************************************************************
							The Whitehead graph of the current PATH is connected and has no 
							cut-vertex. So no disjoint-wave contains this PATH. 
						**********************************************************************/
						FoundPossibleWave = FALSE;
						P_From_Face[TerminalFace][0] = 1;
						FacesVisited[TerminalFace] = FALSE;
						if(NumPathsInWave == 0) break; 
						NumPathsInWave --;
						TerminalFace = FacesVisitedList[NumPathsInWave + 1];
						continue;
												
				/*		printf("\nThe current PATH: %s \n",(char *) *Relators[1]);
						printf("is 'good'. PATH Faces and Paths: ");
						for(j = 1; j <= NumPathsInWave; j++) 
							printf("F%d,P%d,",FacesVisitedList[j],PathsInWave[j]);
							printf("F%d",TerminalFace);				*/
						}
							
					/********************************************************************************** 	
										Check if the CurrentPath is a 'wave'.
							Heegaard now checks if the current PATH P, whose endpoints lie at the 
						barycenters of P's initial and terminal faces F_i and F_t, can be extended 
						to a PATH P' which intersects each of F_i, F_t in an essential properly 
						embedded arc, so P' becomes a wave to some relator of the Heegaard diagram.					
					**********************************************************************************/
				
					FoundPossibleWave = FALSE;
					jj = abs(PathsInWave[1]);
					
					/************************************************************************************			
						1)  Replace two appearances of Pl[jj] and two appearances of Pr[jj] in 
							BdryRelsFace[InitialFace] with '{' and '}' respectively.
						2)  Replace two appearances of Pl[abs(ii)] and two appearances of Pr[abs(ii)]
							in BdryRelsFace[TerminalFace] with '[' and ']' respectively.
						3)  Set FoundPossibleWave TRUE if the edited strings BdryRelsFace[InitialFace] 
							and BdryRelsFace[TerminalFace] have a character in common. 
						4)	Restore BdryRelsFace[InitialFace] and BdryRelsFace[TerminalFace].
					************************************************************************************/		
			
					for(k = 1,tl = Pl[jj]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[InitialFace],tl);
						*q = '{';
						}
					for(k = 1,tr = Pr[jj]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[InitialFace],tr);
						*q = '}';
						}
					for(k = 1,tl = Pl[abs(ii)]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[TerminalFace],tl);
						*q = '[';
						}	
					for(k = 1,tr = Pr[abs(ii)]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[TerminalFace],tr);
						*q = ']';
						}	
					if(strpbrk((char*) BdryRelsFace[InitialFace], (char*) BdryRelsFace[TerminalFace]) != NULL) 
						FoundPossibleWave = TRUE;
					for(k = 1,tl = Pl[jj]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[InitialFace],'{');
						*q = tl;
						}
					for(k = 1,tr = Pr[jj]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[InitialFace],'}');
						*q = tr;
						}
					for(k = 1,tl = Pl[abs(ii)]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[TerminalFace],'[');
						*q = tl;
						}	
					for(k = 1,tr = Pr[abs(ii)]; k <= 2; k++)
						{
						q = (unsigned char *) strchr((char*) BdryRelsFace[TerminalFace],']');
						*q = tr;
						}							
						
					if(FoundPossibleWave)	
						{
						if(Micro_Print != 6 && Micro_Print != 7)
							{
							NumPossibleWavesFound ++;
							if(kk && kk != TOO_LONG)
								{
								if(Micro_Print == 5)
									{
									printf("\n%u) Found a possible 'disjoint-wave': %s \n",NumPossibleWavesFound,(char *) *Relators[1]);
									printf("with Faces and Paths: ");
									for(j = 1; j <= NumPathsInWave; j++) 
										printf("F%d,P%d,",FacesVisitedList[j],PathsInWave[j]);
										printf("F%d",TerminalFace);
									}
								FoundWave = TRUE;	
								goto FOUND_WAVE;
								}					
							if(kk == TOO_LONG) 
								{
								FoundWave = TOO_LONG;
								goto FOUND_WAVE;
								}
							}
						if((Micro_Print == 6 || Micro_Print == 7) && TerminalFace > InitialFace)
							{
							NumPossibleWavesFound ++;
							if(kk && kk != TOO_LONG)
								{
								printf("\n%u) Found a possible 'disjoint-wave': %s \n",NumPossibleWavesFound,(char *) *Relators[1]);
								printf("with Faces and Paths: ");
								for(j = 1; j <= NumPathsInWave; j++) 
									printf("F%d,P%d,",FacesVisitedList[j],PathsInWave[j]);
									printf("F%d",TerminalFace);
								FoundWave = TRUE;
								}					
							if(kk == TOO_LONG) 
								{
								FoundWave = TOO_LONG;
								goto FOUND_WAVE;
								}
							}
						if(Micro_Print == 7)
							{	
							FoundPossibleWave = FALSE;
							P_From_Face[TerminalFace][0] = 1;
							FacesVisited[TerminalFace] = FALSE;
							if(NumPathsInWave == 0) break; 
							NumPathsInWave --;
							TerminalFace = FacesVisitedList[NumPathsInWave + 1];
							continue;
							}
						}						
					}							
				}			
			}	
		}
		 
	if(Micro_Print == 6)
		printf("\nFound %u 'disjoint-wave' or 'disjoint-loop' candidates which traverse a face at most once.",NumPossibleWavesFound);
	if(Micro_Print == 7) printf("\nFound %u minimal 'disjoint-wave or 'disjoint-loop' candidates.",NumPossibleWavesFound);

FOUND_WAVE:
		
	/* Restore Relators[1], NumGenerators and NumRelators. */
	
	NumGenerators = SNumGenerators;
	NumRelators   = SNumRelators;
	
	if(SRelator1 != NULL)
		{
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetPtrSize((char *) SRelator1));
		if(Relators[1] == NULL) Mem_Error();		
		p = SRelator1;
		q = *Relators[1];
		while((*q++ = *p++)) ;	
		DisposePtr((unsigned char *) SRelator1);
		}
		
END:

	for(j = 1; j <= NumPaths; j++) 
		{
		if(PM[j] != NULL) DisposePtr((char *) PM[j]);
		if(PP[j] != NULL) DisposePtr((char *) PP[j]);		
		}
	
	for(j = 1; j <= NumFaces; j++) 
		{
		if(P_From_Face[j])  DisposePtr((int *) P_From_Face[j]);
		if(BdryRelsFace[j]) DisposePtr((char *) BdryRelsFace[j]);
		}
	if(BadPath != NULL)				DisposePtr((unsigned char **) BadPath);	
	if(BdryRelsFace)				DisposePtr((unsigned char **) BdryRelsFace);
	if(FacesVisitedList != NULL) 	DisposePtr((unsigned char *)  FacesVisitedList);
	if(FacesVisited != NULL) 		DisposePtr((unsigned char *)  FacesVisited);
	if(Pl != NULL)					DisposePtr((unsigned char *)  Pl);
	if(PM != NULL) 					DisposePtr((unsigned char **) PM);
	if(PP != NULL) 					DisposePtr((unsigned char **) PP);	
	if(P_From_Face != NULL) 		DisposePtr((int **) 		  P_From_Face);
	if(PM_From != NULL) 			DisposePtr((unsigned char *)  PM_From);
	if(PP_From != NULL) 			DisposePtr((unsigned char *)  PP_From);
	if(PM_To != NULL) 				DisposePtr((unsigned char *)  PM_To);
	if(PP_To != NULL) 				DisposePtr((unsigned char *)  PP_To);
	if(Pr != NULL)					DisposePtr((unsigned char *)  Pr);
	if(PathsInWave != NULL) 		DisposePtr((int *) 			  PathsInWave);
	
	return(FoundWave);	
}

int Check_HS_Strong_IrreducibilityS2(unsigned char NumPathsInWave,int * PathsInWave,unsigned char ** PP,unsigned char ** PM)
{
	unsigned char	*p,
					*q;
					
	int				j,
					k,
					kk;
	
	long			HSS;		
			
	/* Check if the graph of a possible 'wave' is connected and has no cut-vertex. */

	for(k = 1,HSS = 1; k <= NumPathsInWave; k++)	
		{
		j    = abs(PathsInWave[k]);
		HSS += GetPtrSize((char *) PP[j]) - 1;
		}
	
	if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
	Relators[1] = (unsigned char **) NewHandle(HSS);
	if(Relators[1] == NULL) Mem_Error();
	q = *Relators[1];	
	for(k = 1; k <= NumPathsInWave; k++)
		{
		kk = PathsInWave[k];
		if(kk > 0)
			{
			p = PP[kk];
			while( (*q++ = *p++) ) ;
			q--;
			}
		else
			{
			kk = -kk;
			p = PM[kk];
			while( (*q++ = *p++) ) ;
			q--;
			}	
		}
	if(HSS <= Vertices) return(2);	
	return(CP_Find_Primitives(FALSE));
}