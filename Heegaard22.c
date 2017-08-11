#include "Heegaard.h"
#include "Heegaard_Dec.h"

/******************************* Functions in Heegaard22.c ********************************
L 741 Compute_H1(unsigned int* ptr1,unsigned int* ptr2)
L 14  DisAmbiguity_Q(char F1)
L 487 Print_1_Gen(char F1)
L 438 Print_DisAmbiguity_Results(unsigned int MyP,char F1)
L 564 Print_DisAmbiguity_Results2(unsigned int MyP1,unsigned int MyP2,char F1)
L 236 RewriteProperPowers(char z,unsigned int MyP,char F1,unsigned int* ptr1,unsigned int* ptr2)
L 760 Two_Syllable_Lens_Space(unsigned int* ptr1,unsigned int* ptr2,char F1)
********************************************************************************************/

int DisAmbiguity_Q(char F1)
{
	unsigned char	Found_Con_Sum,
					Found_Q,
					*p,
					*q,
					STestRealizability1,
					**Temp;

	int				i,
					j,
					MyNumGenerators,
					MyNumRelators,
					n,
					SDrawingDiagrams;
				
	unsigned int	EXPA,
					EXPB,
					H1,
					*ptr1,
					*ptr2,
					SNumFilled;

	void Print_DisAmbiguity_Results(unsigned int,char);
	void Print_1_Gen(char);
	void Print_DisAmbiguity_Results2(unsigned int,unsigned int,char);
	int  Compute_H1(unsigned int*,unsigned int*);
	int Two_Syllable_Lens_Space(unsigned int*,unsigned int*,char);				

	Found_Con_Sum = FALSE;
	Found_Q = FALSE;

	if(F1)
		{	
		printf("\n\nStabilizing:");		
		Stabilize(TRUE);
		printf("\n\nStabilizing:");	
		Stabilize(TRUE);
		printf("\n\nDeStabilizing:\n");	
		NXMG = (unsigned char*) NewPtr((sizeof(char)*MAX_SAVED_PRES));
		if(NXMG == NULL) Mem_Error();
		Just_Delete_Primitives(FALSE,FALSE);
		for(i = 0; i < NumFilled; i++) UDV[i] = 0;		
		}

	for(i = 0; i < NumFilled; i++) Table1[i] = i;

	qksort1(NumFilled);

	printf("\n\nNote: Ignore presentations with ID numbers greater than %u.",NumFilled);
	
	/*	Look for 2-generator, 2-relator presentations in which one relator is a proper-power or
		a primitive of length one. */

	MyNumRelators = MyNumGenerators = 2;

	ptr1 = (unsigned int *)NewPtr(sizeof(int)*100);
	if(ptr1 == NULL) Mem_Error();
	ptr2 = (unsigned int *)NewPtr(sizeof(int)*100);
	if(ptr2 == NULL) Mem_Error();
	SNumFilled = NumFilled;	
	for(n = SNumFilled - 1; n >= 0; n--)	
		{
		ReadPres = Table1[n];
		NumGenerators = NG[ReadPres];
		NumRelators   = NR[ReadPres];
		if(NumGenerators == 1 && NumRelators <= 1)
			{
			Print_1_Gen(F1);
			continue;
			}
		if(NumGenerators < MyNumGenerators) continue;
		if(NumGenerators > MyNumGenerators) 
			{			
			if(F1 || ComponentNum[ReadPres] == 1) break;
			if(ComponentNum[ReadPres] > 1) continue;
			}
		if(NumRelators != MyNumRelators) continue;
		for(i = 1; i <= NumRelators; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(Relators[i] == NULL) Mem_Error();
			q = *Relators[i];
			p = *SUR[ReadPres][i];
			while( (*q++ = *p++) ) ;
			}
		STestRealizability1 = TestRealizability1;
		SDrawingDiagrams = DrawingDiagrams;
		TestRealizability1 = TRUE;
		DrawingDiagrams = TRUE;
		j = Diagram_1();
		TestRealizability1 = STestRealizability1;
		DrawingDiagrams = SDrawingDiagrams;
		if(j == 1) continue;	
		Diagram_2();

		if(Two_Syllable_Lens_Space(ptr1,ptr2,F1)) continue;
	
		EXPA = EXP[0][2];
		EXPB = EXP[1][2];

		if(EXP[0][1] || EXPA == 1) EXPA = 0;
		if(EXP[1][1] || EXPB == 1) EXPB = 0;

		if(EXPA && EXPB && !Found_Con_Sum)
			{
			Found_Con_Sum = TRUE;
			Print_DisAmbiguity_Results2(EXPA,EXPB,F1);
			continue;
			}
		if(EXPA && !EXPB)
			{
			if(EXP[1][2] == 1 && NEX[0][2] > 1) continue;	/* {A,a} separates. */
			if(RewriteProperPowers('A',EXPA,F1,ptr1,ptr2) == 1) Found_Q = TRUE;
			continue;
			}
		if(EXPB && !EXPA)		
			{
			if(EXP[0][2] == 1 && NEX[1][2] > 1) continue;	/* {B,b} separates. */
			if(RewriteProperPowers('B',EXPB,F1,ptr1,ptr2) == 1) Found_Q = TRUE;
			continue;
			}

		Input = NORMAL;
		j = Check_For_Primitives(1,2);
		if(j == 2)
			{
			Temp 		= Relators[1];
			Relators[1] = Relators[2];
			Relators[2] = Temp;			
			}					
		if(j == 1 || j == 2)
			{			
			Vertices = 2*NumGenerators;
			for(i = 1; i <= Vertices; i++) ZZ[i] = 0;
			LR[1] = GetHandleSize((char **) Relators[1]) - 1;
			LR[2] = GetHandleSize((char **) Relators[2]) - 1;
			Length = LR[1] + LR[2];
			H1 = abs(Compute_H1(ptr1,ptr2));			
			i = Lens_Space();
			if(i == 0)
				{		
				Print_DisAmbiguity_Results(1,F1);
				Found_Q = TRUE;
				}	
			if(Found_Q) continue;			
			}
		
		/* Check for primitive DualRelators. */

		Vertices = 2*NumGenerators;	
		LR[1] = GetHandleSize((char **) Relators[1]) - 1;
		LR[2] = GetHandleSize((char **) Relators[2]) - 1;
		Length = LR[1] + LR[2];		
		Fill_A(NumRelators);
		Input = NORMAL;
		Saved_Vertices = 0;	
		for(i = 1; i <= Vertices; i++) ZZ[i] = 0;	
		if(Find_Flow_A(NORMAL,FALSE)) continue;
		if(Whitehead_Graph()) continue;
		for(i = 1; i <= 2; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) DualRelators[i]));
			if(Relators[i] == NULL) Mem_Error();			
			p = *DualRelators[i];
			q = *Relators[i];
			while( (*q++ = *p++) ) ;			
			}
		Freely_Reduce();
		if(LR[1] == 0)
			{
			P = 0;
			if(LR[2] == 0)
				{
				Print_DisAmbiguity_Results(0,F1);
				continue;
				}
			Temp = Relators[1];
			Relators[1] = Relators[2];
			Relators[2] = Temp;
			Length = LR[1] + LR[2];
			Find_Flow_A(NORMAL,1);
			Print_DisAmbiguity_Results(Length1,F1);
			continue;
			}
		if(LR[2] == 0)
			{
			Length = LR[1] + LR[2];
			Find_Flow_A(NORMAL,1);
			P = Length1;
			Print_DisAmbiguity_Results(0,F1);
			continue;			
			}
		j = Check_For_Primitives(1,2);
		if(j == 1 || j == 2) 
			{
			H1 = abs(Compute_H1(ptr1,ptr2));
			for(i = 1; i <= NumRelators; i++)
				{
				if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
				Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
				if(Relators[i] == NULL) Mem_Error();
				q = *Relators[i];
				p = *SUR[ReadPres][i];
				while( (*q++ = *p++) ) ;
				}
			}						
		if((j == 1 || j == 2) && Lens_Space_D(j,FALSE) == 0)
			{
			Print_DisAmbiguity_Results(1,F1);
			Found_Q = TRUE;		
			}
		if(Found_Q) continue;																	
		}
	if(F1) DisposePtr((unsigned char *) NXMG);
	DisposePtr((unsigned int *) ptr1);
	DisposePtr((unsigned int *) ptr2);
	return(0);
}

int RewriteProperPowers(char z,unsigned int MyP,char F1,unsigned int* ptr1,unsigned int* ptr2)
{
	unsigned char	Flag,
					*p,
					*q,
					G,
					g,
					**Temp,
					x;
				
	int				i,
					j,
					k;
				
	unsigned int 	H1;					

	void Print_DisAmbiguity_Results(unsigned int,char);
	void Print_DisAmbiguity_Results2(unsigned int,unsigned int,char);
	int  Compute_H1(unsigned int*,unsigned int* ptr2);		
            
    if(z < 'a')
        {
        G = z;
        g = z + 32;
        }
    else
        {
        g = z;
        G = g - 32;
        }
        
    /******************************************************************************************
            Replace G^e with G and g^e with g throughout each relator.                         
    ******************************************************************************************/
    
    for(i = 1,Length = 0; i <= NumRelators; i++)
        {
        if(Temp4 != NULL) DisposeHandle((char **) Temp4);
        Temp4 = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
        if(Temp4 == NULL) Mem_Error();
        q = *Temp4;      
        p = *Relators[i];
        Flag = TRUE;
        x = *p;
        while( (x = *p++) )
            {
            if(x != G && x != g) 
            	{
            	*q++ = x;
            	Flag = TRUE;
            	}
			if((x == G || x == g) && Flag == TRUE)
				{
				*q++ = x;
				Flag = FALSE;
				}
            }
        *q = EOS;
		p = *Temp4;
		if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
		Relators[i] = (unsigned char **) NewHandle(q - p + 1);
		if(Relators[i] == NULL) Mem_Error();
		q = *Relators[i];
		while( (*q++ = *p++) ) ; 
		LR[i] = GetHandleSize((char **) Relators[i]) - 1;
		Length += LR[i];                          
        }

	/*	Save copies of R1 and R2 in R3 and R4.	*/

	for(i = 1; i <= 2; i++)
		{
		if(Relators[i + 2] != NULL) DisposeHandle((char **) Relators[i + 2]);
		Relators[i + 2] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
		if(Relators[i + 2] == NULL) Mem_Error();
		p = *Relators[i];
		q = *Relators[i + 2];
		while( (*q++ = *p++) ) ;		
		}

	for(k = 1; k <= 2; k++)
		{
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(2);
		if(Relators[1] == NULL) Mem_Error();
		p = *Relators[1];
		*p++ = G;
		*p = EOS;
		if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
		Relators[2] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[k + 2]));
		if(Relators[2] == NULL) Mem_Error();
		p = *Relators[k + 2];			
		q = *Relators[2];
		while( (*q++ = *p++) ) ;
		LR[1] = 1;
		LR[2] = GetHandleSize((char **) Relators[2]) - 1;
		if(LR[2] == 1)
			{
			p = *Relators[2];
			if(*p == G || *p == g) continue;
			}
		Length = LR[1] + LR[2];			
					
		Vertices = 2*NumGenerators;
		for(i = 1; i <= Vertices; i++) ZZ[i] = 0;
	
		j = Check_For_Primitives(1,2);
	
		if(j == 1 || j == 2) 
			H1 = abs(Compute_H1(ptr1,ptr2));
		if(j == 1 && Lens_Space() == 0)
			{		
			Print_DisAmbiguity_Results(MyP,F1);
			return(1);
			}
		if(j == 2)
			{
			Temp = Relators[1];
			Relators[1] = Relators[2];
			Relators[2] = Temp;
			LR[1] = GetHandleSize((char **) Relators[1]) - 1;
			LR[2] = GetHandleSize((char **) Relators[2]) - 1;
			if(Lens_Space() == 0)
				{		
				Print_DisAmbiguity_Results(MyP,F1);
				return(1);
				}
			} 
	
		if(j == 1 || j == 2)
			Print_DisAmbiguity_Results2(H1,MyP,F1);
		
		/* Check for primitive DualRelators. */
	
		Vertices = 2*NumGenerators;	
		Fill_A(NumRelators);
		Input = NORMAL;
		Saved_Vertices = 0;	
		for(i = 1; i <= Vertices; i++) ZZ[i] = 0;	
		if(Find_Flow_A(NORMAL,FALSE)) return(0);
		if(Whitehead_Graph()) return(0);		
		for(i = 1; i <= 2; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) DualRelators[i]));
			if(Relators[i] == NULL) Mem_Error();			
			p = *DualRelators[i];
			q = *Relators[i];
			while( (*q++ = *p++) ) ;			
			}
		Freely_Reduce();
		if(LR[1] == 0)
			{
			P = 0;
			if(LR[2] == 0)
				{
				Print_DisAmbiguity_Results(0,F1);
				return(1);
				}
			Temp = Relators[1];
			Relators[1] = Relators[2];
			Relators[2] = Temp;
			Length = LR[1] + LR[2];
			Find_Flow_A(NORMAL,1);
			Print_DisAmbiguity_Results(Length1,F1);
			return(1);
			}
		if(LR[2] == 0)
			{
			Length = LR[1] + LR[2];
			Find_Flow_A(NORMAL,1);
			P = Length1;
			Print_DisAmbiguity_Results(0,F1);
			return(1);			
			}	
		j = Check_For_Primitives(1,2);
		if(j == 1 || j == 2) 
			{
			H1 = abs(Compute_H1(ptr1,ptr2));
			for(i = 1; i <= NumRelators; i++)
				{
				if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
				Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
				if(Relators[i] == NULL) Mem_Error();
				q = *Relators[i];
				p = *SUR[ReadPres][i];
				while( (*q++ = *p++) ) ;
				}
			}				
		if((j == 1 || j == 2) && Lens_Space_D(j,FALSE) == 0)
			{
			Print_DisAmbiguity_Results(MyP,F1);
			return(1);		
			}

		if(j == 1 || j == 2)
			Print_DisAmbiguity_Results2(H1,MyP,F1);
		}	
		     
  return(0);      
}   

void Print_DisAmbiguity_Results(unsigned int MyP,char F1)
{
	if(P == 0) 	
		{
		if(F1 == TRUE)
			{
			if(NXMG[ReadPres] == 0)
				printf("\n\n%-19s = S1 X S2",PresName);
			else	
				printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres] + 1);
			}
		else 
			printf("\n\n%-19s Summand %u = S1 X S2",PresName,ComponentNum[ReadPres]);
		}
	if(P == 1) 	
		{
		if(F1 == TRUE)
			{
			if(NXMG[ReadPres] == 0)
				printf("\n\n%-19s = S^3",PresName);
			if(NXMG[ReadPres] == 1)	
				printf("\n\n%-19s = S1 X S2",PresName);
			if(NXMG[ReadPres] > 1)
				printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres]);
			}
		else 
			printf("\n\n%-19s Summand %u = S^3",PresName,ComponentNum[ReadPres]);
		}
	if(P > 1) 	
		{
		if(F1 == TRUE)
			{
			if(NXMG[ReadPres] == 0)
				printf("\n\n%-19s = L(%lu,%lu)",PresName,P,Q);
			if(NXMG[ReadPres] == 1)
				printf("\n\n%-19s = L(%lu,%lu) # S1 X S2",PresName,P,Q);
			if(NXMG[ReadPres] > 1)
				printf("\n\n%-19s = L(%lu,%lu) # %d S1 X S2",PresName,P,Q,NXMG[ReadPres]);
			}
		else 
			printf("\n\n%-19s Summand %u = L(%lu,%lu)",PresName,ComponentNum[ReadPres],P,Q);
		}
	if(MyP == 0) 			printf(" # S1 X S2");
	if(1 < MyP && MyP < 5) 	printf(" # L(%u,1)",MyP);
	if(MyP == 5) 			printf(" # L(5,Q)");
	if(MyP == 6) 			printf(" # L(%u,1)",MyP);
	if(MyP > 6) 			printf(" # L(%u,Q)",MyP);
}

void Print_1_Gen(char F1)
{
	unsigned long MyP;

	if(NumRelators == 1) MyP = GetHandleSize((char **) SUR[ReadPres][1]) - 1;
	if(NumRelators == 0) MyP = 0;
	switch(MyP)
		{
		case 0:
			if(F1 == TRUE)
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = S1 X S2",PresName);
				else	
					printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres] + 1);
				}
			else		
				printf("\n\n%-19s Summand %u = S1 X S2",PresName,ComponentNum[ReadPres]);
			break;
		case 1:
			if(F1 == TRUE)
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = S^3",PresName);
				if(NXMG[ReadPres] == 1)	
					printf("\n\n%-19s = S1 X S2",PresName);
				if(NXMG[ReadPres] > 1)
					printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres]);
				}			
			else
				printf("\n\n%-19s Summand %u = S^3",PresName,ComponentNum[ReadPres]);
			break;
		case 2:
		case 3:
		case 4:
		case 6:
			if(F1 == TRUE)
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = L(%lu,1)",PresName,MyP);
				if(NXMG[ReadPres] == 1)
					printf("\n\n%-19s = L(%lu,1) # S1 X S2",PresName,MyP);
				if(NXMG[ReadPres] > 1)
					printf("\n\n%-19s = L(%lu,1) # %d S1 X S2",PresName,MyP,NXMG[ReadPres]);
				}		
			else
				printf("\n\n%-19s Summand %u = L(%lu,1)",PresName,ComponentNum[ReadPres],MyP);
			break;
		case 5:
			if(F1 == TRUE)
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = L(5,Q)",PresName);
				if(NXMG[ReadPres] == 1)
					printf("\n\n%-19s = L(5,Q) # S1 X S2",PresName);
				if(NXMG[ReadPres] > 1)
					printf("\n\n%-19s = L(5,Q) # %d S1 X S2",PresName,NXMG[ReadPres]);
				}				
			else
				printf("\n\n%-19s Summand %u = L(5,Q)",PresName,ComponentNum[ReadPres]);
			break;
		default:
			if(F1 == TRUE)
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = L(%lu,Q)",PresName,MyP);
				if(NXMG[ReadPres] == 1)
					printf("\n\n%-19s = L(%lu,Q) # S1 X S2",PresName,MyP);
				if(NXMG[ReadPres] > 1)
					printf("\n\n%-19s = L(%lu,Q) # %d S1 X S2",PresName,MyP,NXMG[ReadPres]);
				}				
			else
				printf("\n\n%-19s Summand %u = L(%lu,Q)",PresName,ComponentNum[ReadPres],MyP);
		break;
		}
}
	
void Print_DisAmbiguity_Results2(unsigned int MyP1,unsigned int MyP2,char F1)
{
	unsigned int	Q1 = 8,
					Q2 = 8,
					Temp;
	
	if(MyP2 > MyP1)
		{
		Temp  	= MyP1;
		MyP1 	= MyP2;
		MyP2 	= Temp;
		}
					
	switch(MyP1) /* Set up Q1. */
		{
		case 1:
			Q1 = 0;
			break;
		case 2:
		case 3:
		case 4:
		case 6:
			Q1 = 1;
			break;	
		}			
	switch(MyP2) /* Set up Q2. */
		{
		case 0:
		case 1:
			Q2 = 0;
			break;
		case 2:
		case 3:
		case 4:
		case 6:
			Q2 = 1;
			break;
		}
	switch(MyP1)
		{
		case 1:
			switch(MyP2)
				{
				case 0:
					if(F1 == TRUE)
						{
						if(NXMG[ReadPres] == 0)
							printf("\n\n%-19s = S1 X S2",PresName);
						if(NXMG[ReadPres] > 0)
							printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres] + 1);
						}
					else 
						printf("\n\n%-19s Summand %u = S1 X S2",PresName,ComponentNum[ReadPres]);
					break;
				case 1: 
					if(F1 == TRUE)
						{
						if(NXMG[ReadPres] == 0)
							printf("\n\n%-19s = S^3",PresName);
						if(NXMG[ReadPres] == 1)
							printf("\n\n%-19s = S1 X S2",PresName);
						if(NXMG[ReadPres] > 1)
							printf("\n\n%-19s = %d S1 X S2",PresName,NXMG[ReadPres]);
						}
					else
						printf("\n\n%-19s Summand %u = S^3",PresName,ComponentNum[ReadPres]);
					break;
				case 2:
				case 3:
				case 4:
				case 6:
					if(F1 == TRUE)
						{
						if(NXMG[ReadPres] == 0)
							printf("\n\n%-19s = L(%u,1)",PresName,MyP2);
						if(NXMG[ReadPres] == 1)
							printf("\n\n%-19s = L(%u,1) # S1 X S2",PresName,MyP2);
						if(NXMG[ReadPres] > 1)
							printf("\n\n%-19s = L(%u,1) # %d S1 X S2",PresName,MyP2,NXMG[ReadPres]);						
						}
					else 
						printf("\n\n%-19s Summand %u = L(%u,1)",PresName,ComponentNum[ReadPres],MyP2);	
					break;
				default:
					if(F1 == TRUE)
						{
						if(NXMG[ReadPres] == 0)
							printf("\n\n%-19s = L(%u,Q)",PresName,MyP2);
						if(NXMG[ReadPres] == 1)
							printf("\n\n%-19s = L(%u,Q) # S1 X S2",PresName,MyP2);
						if(NXMG[ReadPres] > 1)
							printf("\n\n%-19s = L(%u,Q) # %d S1 X S2",PresName,MyP2,NXMG[ReadPres]);						
						}
					else 
						printf("\n\n%-19s Summand %u = L(%u,Q)",PresName,ComponentNum[ReadPres],MyP2);		
				}
			break;
		case 2:
		case 3:
		case 4:
		case 6:
			if(F1 == TRUE) 
				{
				if(NXMG[ReadPres] == 0)
					printf("\n\n%-19s = L(%u,1)",PresName,MyP1);
				if(NXMG[ReadPres] == 1)
					printf("\n\n%-19s = L(%u,1) # S1 X S2",PresName,MyP1);
				if(NXMG[ReadPres] > 1)
					printf("\n\n%-19s = L(%u,1) # %d S1 X S2",PresName,MyP1,NXMG[ReadPres]);						
				}
			else 
				printf("\n\n%-19s Summand %u = L(%u,1)",PresName,ComponentNum[ReadPres],MyP1);
			switch(MyP2)
				{
				case 0:
					printf(" # S1 X S2");
					break;
				case 1:
					break;	
				case 2:
				case 3:
				case 4:
				case 6:
					printf(" # L(%u,1)",MyP2);
					break;
				default:
					printf(" # L(%u,Q)",MyP2);
				}
			break;
		default:
			if(Q2 < 2) 	
				{
				if(F1 == TRUE) 
					{
					if(NXMG[ReadPres] == 0)
						printf("\n\n%-19s = L(%u,Q)",PresName,MyP1);
					if(NXMG[ReadPres] == 1)
						printf("\n\n%-19s = L(%u,Q) # S1 X S2",PresName,MyP1);
					if(NXMG[ReadPres] > 1)
						printf("\n\n%-19s = L(%u,Q) # %d S1 X S2",PresName,MyP1,NXMG[ReadPres]);						
					}
				else
					printf("\n\n%-19s Summand %u = L(%u,Q)" ,PresName,ComponentNum[ReadPres],MyP1);
				}
			else
				{
				if(F1 == TRUE) 
					{
					if(NXMG[ReadPres] == 0)
						printf("\n\n%-19s = L(%u,Q1)",PresName,MyP1);
					if(NXMG[ReadPres] == 1)
						printf("\n\n%-19s = L(%u,Q1) # S1 X S2",PresName,MyP1);
					if(NXMG[ReadPres] > 1)
						printf("\n\n%-19s = L(%u,Q1) # %d S1 X S2",PresName,MyP1,NXMG[ReadPres]);						
					}
				else 
					printf("\n\n%-19s Summand %u = L(%u,Q1)",PresName,ComponentNum[ReadPres],MyP1);
				}
			switch(MyP2)
				{
				case 0:
					printf(" # S1 X S2");
					break;
				case 1:
					break;	
				case 2:
				case 3:
				case 4:
				case 6:
					printf(" # L(%u,1)",MyP2);
					break;
				default:
					printf(" # L(%u,Q2)",MyP2);
				}
		}		
}

int Compute_H1(unsigned int* ptr1,unsigned int* ptr2)
{
	unsigned char 	*p,
					x;				
	int				H1;

		ptr1['A'] = ptr1['B'] = ptr1['a'] = ptr1['b'] = 0;
		p = *Relators[1];
		while( (x = *p++) ) ptr1[x] ++;
		ptr2['A'] = ptr2['B'] = ptr2['a'] = ptr2['b'] = 0;
		p = *Relators[2];
		while( (x = *p++) ) ptr2[x] ++;
			
		H1 = (ptr1['A'] - ptr1['a'])*(ptr2['B'] - ptr2['b']) - (ptr2['A'] - ptr2['a'])*(ptr1['B'] - ptr1['b']);
	
		return(H1);
}


int Two_Syllable_Lens_Space(unsigned int* ptr1,unsigned int* ptr2,char F1)
{
	int		p,
			q,
			s,
			t;
			
	unsigned int GCDRV;	
			
	/* Check if R1 = A^pB^t and R2 = A^qB^s with |p|,|q|,|s|, and |t| > 1. */
	
	if(EXP[0][0] > 0  || EXP[1][0] > 0 ) return(0);
	if(EXP[0][1] <= 1 || EXP[1][1] <= 1) return(0);
	if(EXP[0][2] <= 1 || EXP[1][2] <= 1) return(0);
	if(NEX[0][1] != 1 || NEX[1][1] != 1) return(0);
	if(NEX[0][2] != 1 || NEX[1][2] != 1) return(0);
	
	/* R1 = A^pB^t and R2 = A^qB^s with |p|,|q|,|s|, and |t| > 1. */
	/* Call Compute_H1() to get the precise exponents that appear in R1 and R2. */
	
	P = abs(Compute_H1(ptr1,ptr2));
	
	if(ptr1['A']) p =  ptr1['A'];
	if(ptr1['a']) p = -ptr1['a'];
	if(ptr1['B']) t =  ptr1['B'];
	if(ptr1['b']) t = -ptr1['b'];
	if(ptr2['A']) q =  ptr2['A'];
	if(ptr2['a']) q = -ptr2['a'];
	if(ptr2['B']) s =  ptr2['B'];
	if(ptr2['b']) s = -ptr2['b'];

	GCDRV = GCD(abs(p),abs(q));
	Recip_Q = -Recip_Q;
	if(GCDRV != 1) return(0);
	if(p > 0 && q < 0) Recip_P = -Recip_P;
	if(p < 0 && q > 0) Recip_P = -Recip_P;
		
	Q = labs(t*Recip_P - s*Recip_Q);	
	Q = Recip_Mod_P(P,Q);
	
	Print_DisAmbiguity_Results(1,F1);
	return(1);
}
