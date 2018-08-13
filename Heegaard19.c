#include "Heegaard.h"
#include "Heegaard_Dec.h"
				
/****************************** Functions in Heegaard19.c *****************************************
L 4269 CheckDualRelator(char MissingGen,int MyCompNum)
L 3532 CheckForAltExpSigns(char WhichRelator, char WhichGen)
L  743 Do_Aut_SF(int Num)
L 4185 Genus3ET(int OrbitNum,int MyCompNum,char F1)
L 2168 Genus_Two_Essential_Tori(int OrbitNum,int MyCompNum,char F1)
L 2882 Genus_Two_Essential_Torus_Betas(char F2)
L  123 Genus_Two_Seifert_Fibered(int OrbitNum,char F1)
L 3597 Get2BKorLPs(char WhichRelator,char WhichGen,unsigned int* Ptr1,unsigned int* Ptr2)
L 3202 Get_Betas2(char WhichRelator,char WhichSquare)
L  495 Get_Genus_2_SF_EXPS1(void)
L  623 Get_Genus_2_SF_EXPS2(void)
L 2694 Get_Genus_2_EXPS(void)
L  932 Get_SF_Alphas1(int Num)
L 1391 Get_SF_Alphas2(int Num)
L 1182 Get_SF_Invariants(int OrbitNum,char F1)
L 3689 GetAlpha2(char WhichRelator,char WhichGen)
L 3745 GetAlpha2Sub1(char WhichRelator,char WhichGen)
L 3949 GetAlpha2Sub2(char WhichRelator,char WhichGen)
L 4131 Init_Genus_Three_Essential_Tori(int* MyTable,int MyStart,int MyCompNum,char F1)
L 2126 Init_Genus_Two_Essential_Tori(int* MyTable,int MyStart,int MyCompNum,char F1)
L   33 Init_Genus_Two_Seifert_Fibered(int* MyTable,int MyStart,int MyCompNum)
L 3390 Print_ET_Data(int MyCompNum)
L 1863 SF_Sort_And_Print(int H1, int n, int A1, int A2, int A3, int B1, int B2, int B3,
	   int NumSolns, int* SolV)
L 3329 Stow_ET_Data(int MyCompNum,char FET,int P0,int P1,int P2,int P3,int P4,int P5,int P6,int P7,int P8)
L 2103 Test_Transverse(void)
********************************************************************************************/				

int Init_Genus_Two_Seifert_Fibered(int* MyTable,int MyStart,int MyCompNum)
{
	unsigned char	*p,
					*q;
					
	int				i,
					m,
					n,
					MultipleSolns,
					NumSFChecked,
					NumSFFound;

	/****** Check which genus two presentations are Seifert Fibered. ******/	

	for(n = MyStart,NumSFChecked = NumSFFound = MultipleSolns = 0; n >= 0; n--) 
		{
		ReadPres 		= MyTable[n];
		if(CS[ComponentNum[ReadPres]] == 1) continue;
		if(ComponentNum[ReadPres] >  MyCompNum) continue;
		if(ComponentNum[ReadPres] <  MyCompNum) return(n);
		NumGenerators 	= NG[ReadPres];
		NumRelators 	= NR[ReadPres];
		if(NumGenerators != 2) continue;
		if(NumRelators > 2) continue;
		Vertices		= 2*NumGenerators;
		Length 			= SURL[ReadPres];
	    for(i = 1; i <= NumRelators; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(Relators[i] == NULL) Mem_Error();
			q = *Relators[i];    
			p = *SUR[ReadPres][i];
			while( (*q++ = *p++) ) ;
			}
		NumSFChecked ++;
		if(NumSFChecked > 100) return(n);
		SFSolV[1] = ReadPres;
		SFSolV[2] = MyCompNum;
		SFSolV[3] = NumRelators;
		m = Genus_Two_Seifert_Fibered(ReadPres + 1,0);
		if(m == 13 || m == 14) 
			{
			NumSFFound ++;
			if(B10B11Finite && FoundFiniteSF == FALSE && (Batch == 10 || Batch == 11)) return(n);
			}
		if(m == 14) MultipleSolns ++;	
		if(NumSFFound > MultipleSolns) 
			{
			if(SFSols[MyCompNum]) DisposePtr((int*) SFSols[MyCompNum]);
			SFSols[MyCompNum] = (int*) NewPtr(sizeof(int)*20);
			if(SFSols[MyCompNum] == NULL) Mem_Error();
			for(i = 0; i < 20; i++) SFSols[MyCompNum][i] = SFSolV[i];
			return(n);
			}
		if(MultipleSolns == 1)
			{
			if(SFSols[MyCompNum]) DisposePtr((int*) SFSols[MyCompNum]);
			SFSols[MyCompNum] = (int*) NewPtr(sizeof(int)*20);
			if(SFSols[MyCompNum] == NULL) Mem_Error();
			for(i = 0; i < 20; i++) SFSols[MyCompNum][i] = SFSolV[i];			
			}	
		}
			
	if(NumSFFound == 1)
		{
		if(NumSFChecked == 1)
			printf("\n\n Heegaard checked one presentation, which was SF.");			
		else	
			printf("\n\n Heegaard found one SF presentation in the %d presentations checked.",NumSFChecked);
		}
	if(NumSFFound > 1)
		{
		printf("\n\n Heegaard found %d SF presentations in the %d presentations checked.",NumSFFound,NumSFChecked);
		}
	if(MultipleSolns && NumSFFound == MultipleSolns)
		{
		printf("\n\n		A Potential Seifert Fibration Ambiguity Exists!");
		printf("\n These ambiguities arise in the following way: Suppose M = ±SF(0;e;B1/A1,B2/A2,B3/A3).");
		printf("\n Then, given A1,A2,A3,B1, and B2, which Heegaard computes, there must exist integers"); 
		printf("\n B3 and e with gcd(A3,B3) = 1 such that at least one of:");
		printf("\n 	|H1(M)| = B1*A2*A3 + A1*B2*A3 + A1*A2*B3 - e*A1*A2*A3,");
		printf("\n 	|H1(M)| = (A1-B1)*A2*A3 + A1*(A2-B2)*A3 + A1*A2*B3 - e*A1*A2*A3");
		printf("\n is satisfied. Generally, there is only one solution with gcd(A3,B3) = 1.");
		printf("\n However, there may by two solutions when 2*A3(A1*B2+A2*B1) = 0 mod A1*A2.");
		}
	
	return(n);		
}
		
int Genus_Two_Seifert_Fibered(int OrbitNum,char F1)
{
char			CheckedRelatorTwo,
				SF;

unsigned char	*p,
				*q,
				**Copy_Of_Rel_3[3],
				**Temp,
				x;
							
int				i,
				NumSolns,
				NumTries;
				
unsigned int	*ptr1,
				*ptr2;				
				
long			H1;

unsigned long	SLength;			
					
	SF = FALSE;
				
	if(NumRelators > 2) 	return(1);
	if(NumGenerators != 2) 	return(2);
	
	/** SFSolV[] has the form: [Flag,ReadPres,MyCompNum,NumRelators,e,B1,A1,B2,A2,B3,A3,e',B1',A1',B2',A2',B3',A3'] **/

	/**********************************************************************************
				Save a copy of the current relators in Copy_Of_Rel_3[]. 
	**********************************************************************************/
	
	for(i = 1; i <= NumRelators; i++)
		{
		Copy_Of_Rel_3[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
		if(Copy_Of_Rel_3[i] == NULL) Mem_Error();
		p = *Copy_Of_Rel_3[i];
		q = *Relators[i];
		while( (*p++ = *q++) ) ;                    
		}
		
	/*********************************************************************************
				If there are two relators, check for S1 X S2.
	*********************************************************************************/
	
	if(NumRelators == 2)
		{
		ptr1 = (unsigned int *)NewPtr(sizeof(int)*100);
		if(ptr1 == NULL) Mem_Error();
		ptr2 = (unsigned int *)NewPtr(sizeof(int)*100);
		if(ptr2 == NULL) Mem_Error();

		ptr1['A'] = ptr1['B'] = ptr1['a'] = ptr1['b'] = 0;
		p = *Relators[1];
		while( (x = *p++) ) ptr1[x] ++;
		ptr2['A'] = ptr2['B'] = ptr2['a'] = ptr2['b'] = 0;
		p = *Relators[2];
		while( (x = *p++) ) ptr2[x] ++;
			
		H1 = (ptr1['A'] - ptr1['a'])*(ptr2['B'] - ptr2['b']) - (ptr2['A'] - ptr2['a'])*(ptr1['B'] - ptr1['b']);
	  	
		if((ptr1['A'] == 0 || ptr1['a'] == 0) && (ptr1['B'] == 0 || ptr1['b'] == 0))
			{
			Vertices = 2*NumGenerators;
			SLength = Length;
			Length = GetHandleSize((char **)Relators[1]) - 1;
			Find_Flow_A(NORMAL,1);			
			Length = SLength;		
			if(Length1 == 1) 
				{
				if(H1 == 0)
					{
					FoundSF = TRUE;
					printf("\n\nA Relator is primitive, and the manifold of Orbit %d is S1 X S2.",OrbitNum);
					if(B10B11Recognized) 
						{
						SFSolV[0] = 1;
						SFSolV[4] = 1;
						SFSolV[5] = 0;						
						}
					DisposePtr((unsigned int *) ptr1);
					DisposePtr((unsigned int *) ptr2);  		
					return(13);
					}
				Length = GetHandleSize((char **)Relators[1]) + GetHandleSize((char **)Relators[2]) - 2;	
				if(Lens_Space()) 
					{
					DisposePtr((unsigned int *) ptr1);
					DisposePtr((unsigned int *) ptr2);
					return(1);
					}
				FoundSF = TRUE;
				FoundFiniteSF = TRUE;
				printf("\n\nA Relator is primitive, so the manifold of Orbit %d is a Lens space: L(%lu,%lu)",OrbitNum,P,Q);
				if(B10B11Finite || B10B11Recognized) 
					{
					SFSolV[0] = 2;
					SFSolV[4] = Q;
					SFSolV[5] = P;
					}
				DisposePtr((unsigned int *) ptr1);
				DisposePtr((unsigned int *) ptr2);					
				return(13);
				}
			}
		if((ptr2['A'] == 0 || ptr2['a'] == 0) && (ptr2['B'] == 0 || ptr2['b'] == 0))
			{			
			Vertices = 2*NumGenerators;
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[2]));
			if(Relators[1] == NULL) Mem_Error();
			p = *Relators[1];
			q = *Copy_Of_Rel_3[2];
			while( (*p++ = *q++) ) ;
			if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
			Relators[2] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[1]));
			if(Relators[2] == NULL) Mem_Error();
			p = *Relators[2];
			q = *Copy_Of_Rel_3[1];
			while( (*p++ = *q++) ) ;
			SLength = Length;
			Length = GetHandleSize((char **)Relators[1]) - 1;
			Find_Flow_A(NORMAL,1);						
			Length = SLength;		
			if(Length1 == 1) 
				{
				if(H1 == 0)
					{
					FoundSF = TRUE;
					printf("\n\nA Relator is primitive, and the manifold of Orbit %d is S1 X S2.",OrbitNum);
					if(B10B11Recognized) 
						{
						SFSolV[0] = 3;
						SFSolV[4] = 1;
						SFSolV[5] = 0;
						}					
					DisposePtr((unsigned int *) ptr1);
					DisposePtr((unsigned int *) ptr2);  		
					return(13);
					}
				Length = GetHandleSize((char **)Relators[1]) + GetHandleSize((char **)Relators[2]) - 2;	
				if(Lens_Space()) 
					{
					DisposePtr((unsigned int *) ptr1);
					DisposePtr((unsigned int *) ptr2);
					return(1);
					}
				FoundSF = TRUE;
				FoundFiniteSF = TRUE;
				printf("\n\nA Relator is primitive, so the manifold of Orbit %d is a Lens space: L(%lu,%lu)",OrbitNum,P,Q);
				if(B10B11Finite || B10B11Recognized)				
					{
					SFSolV[0] = 4;
					SFSolV[4] = Q;
					SFSolV[5] = P;
					}				 
				DisposePtr((unsigned int *) ptr1);
				DisposePtr((unsigned int *) ptr2);					
				return(13);					
				}
			}
							
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[1]));
		p = *Relators[1];
		q = *Copy_Of_Rel_3[1];
		while( (*p++ = *q++) ) ;
		if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
		Relators[2] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[2]));
		p = *Relators[2];
		q = *Copy_Of_Rel_3[2];
		while( (*p++ = *q++) ) 
		;
    	DisposePtr((unsigned int *) ptr1);
    	DisposePtr((unsigned int *) ptr2);
    	}
		
	CheckedRelatorTwo = FALSE;
	CHECKRELATORTWO:
						
		Vertices = 2*NumGenerators;
		SLength = Length;
		Length = GetHandleSize((char **)Relators[1]) - 1;
		i = Find_Flow_A(NORMAL,1);	
		Length = SLength;

		NumTries = 0;
	TRYAGAIN:
		if(NumTries++ > 1) goto END;
	
		if(Get_Genus_2_SF_EXPS1()) return(5);

		if(NumRelators == 2) i = Get_Genus_2_SF_EXPS2();
		if(i) return(6);
	/*
	Print_Relators(Relators,NumRelators);
		printf("\n");
		for(i = 0; i < 3; i++) printf(" EXPA1_SF[%d] = %3d",i,EXPA1_SF[i]);
		printf("\n");
		for(i = 0; i < 3; i++) printf(" NEXA1_SF[%d] = %3d",i,NEXA1_SF[i]);
		printf("\n");
		for(i = 0; i < 3; i++) printf(" EXPB1_SF[%d] = %3d",i,EXPB1_SF[i]);
		printf("\n");
		for(i = 0; i < 3; i++) printf(" NEXB1_SF[%d] = %3d",i,NEXB1_SF[i]);
		printf("\n");
		printf(" NumAEXPS = %d, NumBEXPS  = %d",NumAEXPS, NumBEXPS);	
	if(NumRelators > 1)
		{	
		printf("\n\n");
		for(i = 0; i < 6; i++) printf(" EXPA2_SF[%d] = %3d",i,EXPA2_SF[i]);
		printf("\n");
		for(i = 0; i < 6; i++) printf(" NEXA2_SF[%d] = %3d",i,NEXA2_SF[i]);
		printf("\n");
		for(i = 0; i < 6; i++) printf(" EXPB2_SF[%d] = %3d",i,EXPB2_SF[i]);
		printf("\n");
		for(i = 0; i < 6; i++) printf(" NEXB2_SF[%d] = %3d",i,NEXB2_SF[i]);
		}																		*/																				

		if(NumAEXPS == 1 && NumBEXPS == 1) 
			{
			if(NEXA1_SF[0] == 1 && NEXB1_SF[0] == 1)
				{
				SF = TRUE;
				Get_SF_Alphas1(1);
				NumSolns = 0;
				if(Get_SF_Invariants(OrbitNum,F1) == 5) NumSolns = 2;
				goto END;
				}
			}
		if(NumAEXPS == 2 && NumBEXPS == 1)
			{
			if(abs(EXPA1_SF[0] - EXPA1_SF[1]) == 1)
				{
				SF = TRUE;
				Get_SF_Alphas1(2);
				NumSolns = 0;
				if(Get_SF_Invariants(OrbitNum,F1) == 5) NumSolns = 2;
				goto END;
				}
			if((NEXB1_SF[0] == 2) && (abs(EXPB1_SF[0]) == 1) && (EXPA1_SF[0]*EXPA1_SF[1] < 0))
				{
				if(Do_Aut_SF(1) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;
				}
			if((NEXB1_SF[0] == 2) && (EXPA1_SF[0]*EXPA1_SF[1] == -1))
				{
				SF = TRUE;			/* R = AB^saB^S: SF over the Mobius band. */
				FoundSF = TRUE;
				if(NumRelators == 1)
				printf("\n\nA relator has the form AB^SaB^S ==> SF over the Mobius band with one exceptional fiber of index S = %d.",abs(EXPB1_SF[0]));
				else
				printf("\n\nA relator has the form AB^SaB^S ==> SF over RP^2 with one or two exceptional fibers, one of index S = %d.",abs(EXPB1_SF[0]));				 		
				if(B10B11Recognized)
					{
					if(NumRelators == 1) SFSolV[0] = 5;
					else SFSolV[0] = 6;
					}	
				}		
			}
		if(NumAEXPS == 1 && NumBEXPS == 2)
			{
			if(abs(EXPB1_SF[0] - EXPB1_SF[1]) == 1)
				{
				SF = TRUE;
				Get_SF_Alphas1(3);
				NumSolns = 0;
				if(Get_SF_Invariants(OrbitNum,F1) == 5) NumSolns = 2;
				goto END;
				}
			if((NEXA1_SF[0] == 2) && (abs(EXPA1_SF[0]) == 1) && (EXPB1_SF[0]*EXPB1_SF[1] < 0))
				{
				if(Do_Aut_SF(2) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;
				}
			if((NEXA1_SF[0] == 2) && (EXPB1_SF[0]*EXPB1_SF[1] == -1))
				{
				SF = TRUE;			/* R = A^PBA^Pb: SF over the Mobius band. */
				FoundSF = TRUE;
				if(NumRelators == 1)
				printf("\n\nA relator has the form A^PBA^Pb ==> SF over the Mobius band with one exceptional fiber of index P = %d.",abs(EXPA1_SF[0])); 
				else
				printf("\n\nA relator has the form A^PBA^Pb ==> SF over RP^2 with one or two exceptional fibers, one of index P = %d.",abs(EXPA1_SF[0])); 						
				if(B10B11Recognized)
					{
					if(NumRelators == 1) SFSolV[0] = 5;
					else SFSolV[0] = 6;
					}	
				}		
			}
		if(NumAEXPS == 2 && NumBEXPS == 2)
			{
			if(EXPB1_SF[0]*EXPB1_SF[1] == 2 && EXPA1_SF[0]*EXPA1_SF[1] < 0 && (abs(EXPA1_SF[0]) == 1 || abs(EXPA1_SF[1]) == 1))
				{
				if(Do_Aut_SF(3) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;
				}
			if(EXPA1_SF[0]*EXPA1_SF[1] == 2 && EXPB1_SF[0]*EXPB1_SF[1] < 0 && (abs(EXPB1_SF[0]) == 1 || abs(EXPB1_SF[1]) == 1))
				{
				if(Do_Aut_SF(4) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;
				}		
			}	
		if(NumAEXPS == 3 && NumBEXPS == 1 && abs(EXPB1_SF[0]) == 1)
			{
			if(abs(EXPA1_SF[0] - EXPA1_SF[1]) == 1 && EXPA1_SF[0]*EXPA1_SF[2] < 0)
				{
				if(Do_Aut_SF(5) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}
			if(abs(EXPA1_SF[0] - EXPA1_SF[2]) == 1 && EXPA1_SF[0]*EXPA1_SF[1] < 0)
				{
				if(Do_Aut_SF(6) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}
			if(abs(EXPA1_SF[1] - EXPA1_SF[2]) == 1 && EXPA1_SF[0]*EXPA1_SF[1] < 0)
				{
				if(Do_Aut_SF(7) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}								
			}
		if(NumAEXPS == 1 && NumBEXPS == 3 && abs(EXPA1_SF[0]) == 1)
			{
			if(abs(EXPB1_SF[0] - EXPB1_SF[1]) == 1 && EXPB1_SF[0]*EXPB1_SF[2] < 0)
				{
				if(Do_Aut_SF(8) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}
			if(abs(EXPB1_SF[0] - EXPB1_SF[2]) == 1 && EXPB1_SF[0]*EXPB1_SF[1] < 0)
				{
				if(Do_Aut_SF(9) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}
			if(abs(EXPB1_SF[1] - EXPB1_SF[2]) == 1 && EXPB1_SF[0]*EXPB1_SF[1] < 0)
				{
				if(Do_Aut_SF(10) == TOO_LONG) return(TOO_LONG);
				goto TRYAGAIN;			
				}								
			}

END:
		
		if(NumRelators == 2 && SF == FALSE && CheckedRelatorTwo == FALSE)
			{
			CheckedRelatorTwo = TRUE;
			for(i = 1; i <= NumRelators; i++)
				{
				if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
				Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[i]));
				if(Relators[i] == NULL) Mem_Error();
				p = *Relators[i];	
				q = *Copy_Of_Rel_3[i];
				while( (*p++ = *q++) ) ;                    
				}
			Temp 		= Relators[1];
			Relators[1] = Relators[2];
			Relators[2] = Temp;
			goto CHECKRELATORTWO;		
			}	

		for(i = 1; i <= NumRelators; i++) if(Copy_Of_Rel_3[i]) 
			{
			if(Copy_Of_Rel_3[i] != NULL) DisposeHandle((char **) Copy_Of_Rel_3[i]);
			Copy_Of_Rel_3[i] = NULL;
			}

		if(NumSolns == 2) return(14);
		if(SF == TRUE) return(13);
		return(0);
}


int Get_Genus_2_SF_EXPS1(void)
{
    /*********************************************************************************************
        This routine determines the exponents with which each generator appears in Relators[1].
    These exponents are left in the arrays EXPA1_SF[] and EXPB1_SF[]. The routine also counts
    the number of times each exponent of each generator appears in Relators[1], and saves these
    values in the arrays NEXA1_SF[] and NEXB1_SF[]. 
    	If Relators[1] has minimal length and Relators[1] is an SF relator, then no generator
    can appear in Relators[1] with more than 3 exponents. (Note exponents are signed here, so 
    e and -e are different exponents.)
    *********************************************************************************************/    
    						
	unsigned char  	i,
					*p,
					x,
					y;
						
	int   			ex,
					sex,
					*q,
					*r;
    
    if(GetHandleSize((char**) Relators[1]) < 3) return(1);  /* Relators[1] is either empty, or a primitive! */
                           
    for(i = 0; i < 3; i++) NEXA1_SF[i] = NEXB1_SF[i] = EXPA1_SF[i] = EXPB1_SF[i] = 0;
	
	p = *Relators[1];
	x = *p++;
	if(!x) return(2);			/* Relators[1] is empty!  */
	ex = 1;
	while(*p == x)
		{
		ex++;
		p++;
		}
	sex = ex;
	ex = 0;
	if(*p) x = *p;
	else return(3); 			/* Relators[1] is a proper power!  */
	while( (y = *p++) )
		{
		if(x == y)
			ex++;
		else
			{
			if(x == 'A' || x == 'a') 
				{
				q = EXPA1_SF;
				r = NEXA1_SF;
				}
			else
				{
				q = EXPB1_SF;
				r = NEXB1_SF;
				}
			if(x > 96) ex = -ex;		
			for(x = 0; x < 3 && ex != q[x] && q[x]; x++) ;
			if(x == 3) return(4);							/* Not Genus 2 SF! */
			q[x] = ex;
			r[x]++;
			ex = 1;    
			}
		x = y;
		}
	y = **Relators[1];        
	if(x == y)
		{
		if(x == 'A' || x == 'a') 
			{
			q = EXPA1_SF;
			r = NEXA1_SF;
			}
		else
			{
			q = EXPB1_SF;
			r = NEXB1_SF;
			}
		ex += sex;	
		if(x > 96) ex = -ex;		
		for(x = 0; x < 3 && ex != q[x] && q[x]; x++) ;
		if(x == 3) return(5);							/* Not Genus 2 SF! */
		q[x] = ex;
		r[x]++;
		}
	else
		{
		if(x == 'A' || x == 'a') 
			{
			q = EXPA1_SF;
			r = NEXA1_SF;
			}
		else
			{
			q = EXPB1_SF;
			r = NEXB1_SF;
			}
		if(x > 96) ex = -ex;		
		for(x = 0; x < 3 && ex != q[x] && q[x]; x++) ;
		if(x == 3) return(6);							/* Not Genus 2 SF! */
		q[x] = ex;
		r[x]++;
		
		ex = sex;
		x = y;
		
		if(x == 'A' || x == 'a') 
			{
			q = EXPA1_SF;
			r = NEXA1_SF;
			}
		else
			{
			q = EXPB1_SF;
			r = NEXB1_SF;
			}
		if(x > 96) ex = -ex;		
		for(x = 0; x < 3 && ex != q[x] && q[x]; x++) ;
		if(x == 3) return(7);							/* Not Genus 2 SF! */
		q[x] = ex;
		r[x]++;
		}
    
    for(i = NumAEXPS = 0; i < 3; i++) if(EXPA1_SF[i]) NumAEXPS ++;
    for(i = NumBEXPS = 0; i < 3; i++) if(EXPB1_SF[i]) NumBEXPS ++;
    
    return(0);            
}

int Get_Genus_2_SF_EXPS2(void)
{
    /******************************************************************************************
        This routine does two things. First, it determines the exponents with which each 
    generator appears in Relators[2]. It leaves these exponents in the six columns of the 
    arrays EXPA2_SF[] and EXPB2_SF[].
        Second, the routine counts the number of appearances of each exponent and leaves
    these counts in the arrays NEXA2_SF[] and NEXB2_SF[].
    ******************************************************************************************/    
    						
	unsigned char  	i,
					*p,
					x,
					y;
						
	int   			ex,
					sex,
					*q,
					*r;
                               
    for(i = 0; i < 6; i++) NEXA2_SF[i] = NEXB2_SF[i] = EXPA2_SF[i] = EXPB2_SF[i] = 0;
	
	p = *Relators[2];
	x = *p++;
	if(!x) return(2);			/* Relators[2] is empty!  */
	ex = 1;
	while(*p == x)
		{
		ex++;
		p++;
		}
	sex = ex;
	ex = 0;
	if(*p) x = *p;
	while( (y = *p++) )
		{
		if(x == y)
			ex++;
		else
			{
			if(x == 'A' || x == 'a') 
				{
				q = EXPA2_SF;
				r = NEXA2_SF;
				}
			else
				{
				q = EXPB2_SF;
				r = NEXB2_SF;
				}
			if(x > 96) ex = -ex;		
			for(x = 0; x < 6 && ex != q[x] && q[x]; x++) ;
			if(x == 6) return(4);							/* Too Many Exponents! */
			q[x] = ex;
			r[x]++;
			ex = 1;    
			}
		x = y;
		}
	y = **Relators[2];        
	if(x == y)
		{
		if(x == 'A' || x == 'a') 
			{
			q = EXPA2_SF;
			r = NEXA2_SF;
			}
		else
			{
			q = EXPB2_SF;
			r = NEXB2_SF;
			}
		ex += sex;	
		if(x > 96) ex = -ex;		
		for(x = 0; x < 6 && ex != q[x] && q[x]; x++) ;
		if(x == 6) return(5);							/* Too Many Exponents! */
		q[x] = ex;
		r[x]++;
		}
	else
		{
		if(x == 'A' || x == 'a') 
			{
			q = EXPA2_SF;
			r = NEXA2_SF;
			}
		else
			{
			q = EXPB2_SF;
			r = NEXB2_SF;
			}
		if(x > 96) ex = -ex;		
		for(x = 0; x < 6 && ex != q[x] && q[x]; x++) ;
		if(x == 6) return(6);							/* Too Many Exponents! */
		q[x] = ex;
		r[x]++;
		
		ex = sex;
		x = y;
		
		if(x == 'A' || x == 'a') 
			{
			q = EXPA2_SF;
			r = NEXA2_SF;
			}
		else
			{
			q = EXPB2_SF;
			r = NEXB2_SF;
			}
		if(x > 96) ex = -ex;		
		for(x = 0; x < 6 && ex != q[x] && q[x]; x++) ;
		if(x == 6) return(7);							/* Too Many Exponents! */
		q[x] = ex;
		r[x]++;
		}
    
return(0);            
}

int Do_Aut_SF(int Num)
{
char			x,
				y;
			
unsigned char	*p,
				**Temp;			
			
int				i,
				ii,
				j,
				k;	
		
unsigned long	SLength;				

	if(Num == 1)
		{
		if(EXPB1_SF[0] > 0) 
			x = 'B';
		else 
			x = 'b';
		if(abs(EXPA1_SF[0]) < abs(EXPA1_SF[1]))
			i = 0;
		else
			i = 1;
		if(EXPA1_SF[i] > 0)
			y = 'A';
		else
			y = 'a';
		k = abs(EXPA1_SF[i]);
		}
	if(Num == 2)
		{
		if(EXPA1_SF[0] > 0) 
			x = 'A';
		else 
			x = 'a';
		if(abs(EXPB1_SF[0]) < abs(EXPB1_SF[1]))
			i = 0;
		else
			i = 1;
		if(EXPB1_SF[i] > 0)
			y = 'B';
		else
			y = 'b';
		k = abs(EXPB1_SF[i]);
		}	
	if(Num == 3)
		{
		if(EXPB1_SF[0] > 0) 
			x = 'B';
		else 
			x = 'b';
		if(abs(EXPA1_SF[0]) > abs(EXPA1_SF[1]))
			i = 0;
		else
			i = 1;
		if(EXPA1_SF[i] > 0)
			y = 'A';
		else
			y = 'a';
		k = abs(EXPA1_SF[i]);
		}
	if(Num == 4)
		{
		if(EXPA1_SF[0] > 0) 
			x = 'A';
		else 
			x = 'a';
		if(abs(EXPB1_SF[0]) > abs(EXPB1_SF[1]))
			i = 0;
		else
			i = 1;
		if(EXPB1_SF[i] > 0)
			y = 'B';
		else
			y = 'b';
		k = abs(EXPB1_SF[i]);
		}
	if(Num == 5)
		{
		if(EXPB1_SF[0] > 0) 
			x = 'B';
		else 
			x = 'b';
		if(EXPA1_SF[2] > 0)
			y = 'A';
		else
			y = 'a';
		k = abs(EXPA1_SF[2]);
		}
	if(Num == 6)
		{
		if(EXPB1_SF[0] > 0) 
			x = 'B';
		else 
			x = 'b';
		if(EXPA1_SF[1] > 0)
			y = 'A';
		else
			y = 'a';
		k = abs(EXPA1_SF[1]);
		}					
	if(Num == 7)
		{
		if(EXPB1_SF[0] > 0) 
			x = 'B';
		else 
			x = 'b';
		if(EXPA1_SF[0] > 0)
			y = 'A';
		else
			y = 'a';
		k = abs(EXPA1_SF[0]);
		}		
	if(Num == 8)
		{
		if(EXPA1_SF[0] > 0) 
			x = 'A';
		else 
			x = 'a';
		if(EXPB1_SF[2] > 0)
			y = 'B';
		else
			y = 'b';
		k = abs(EXPB1_SF[2]);
		}
	if(Num == 9)
		{
		if(EXPA1_SF[0] > 0) 
			x = 'A';
		else 
			x = 'a';
		if(EXPB1_SF[1] > 0)
			y = 'B';
		else
			y = 'b';
		k = abs(EXPB1_SF[1]);
		}
	if(Num == 10)
		{
		if(EXPA1_SF[0] > 0) 
			x = 'A';
		else 
			x = 'a';
		if(EXPB1_SF[0] > 0)
			y = 'B';
		else
			y = 'b';
		k = abs(EXPB1_SF[0]);
		}										
	
	/****************************************************************************************************
		In order to get an SF relator in which one of the generators appears only with exponents ±2, we
		create an additional relator of the form xy^kxy^k, which automorphisms will reduce to x^2.
		This will force the SF relator to have standard form in which one of the generators appears
		only with exponents ±2.
	*****************************************************************************************************/
				
	ii = NumRelators + 1;
	if(Relators[ii] != NULL) DisposeHandle((char **) Relators[ii]);
	Relators[ii] = (unsigned char **) NewHandle((2*k + 3)*sizeof(char));
	if(Relators[ii] == NULL) Mem_Error();			
	p = *Relators[ii];
	*p++ = x;
	for(j = 0; j < k; j++) *p++ = y;
	*p++ = x;
	for(j = 0; j < k; j++) *p++ = y;
	*p = EOS;
	
	Temp 			= Relators[ii];
	Relators[ii] 	= Relators[ii-1];
	Relators[ii-1] 	= Temp;			
	
	NumGenerators 	= 2;
	NumRelators 	= ii;
	Vertices 		= 4;
	SLength 		= Length;	
	for(i = 1, Length = 0L; i <= 2; i++) Length += GetHandleSize((char **) Relators[i]) - 1;
	Find_Flow_A(NORMAL,2);
	Temp 			= Relators[ii];
	Relators[ii] 	= Relators[ii-1];
	Relators[ii-1] 	= Temp;	
	NumRelators 	= ii - 1;
	Length 			= SLength;
	
return(0);
}

int Get_SF_Alphas1(int Num)
{
char		F1,
			FA,
			FB;

int			Alp3A,
			Alp3B,
			i,
			j,
			MA,
			MB,
			NA,
			NB;

	if(Num == 1)
		{
		Alphas[1] = abs(EXPA1_SF[0]);
		Alphas[2] = abs(EXPB1_SF[0]);
		if(NumRelators == 1) return(0);
		if(NumRelators == 2)
			{			
			/******************************************
			 	Get tentative Betas[1] and Betas[2]. 
			******************************************/
			
			for(i = 0, Betas[1] = 0; i < 6; i++) if(EXPA2_SF[i] && abs(EXPA2_SF[i]) != Alphas[1])
				{
				Betas[1] = EXPA2_SF[i] % Alphas[1];
				if(Betas[1] < 0) Betas[1] += Alphas[1];
				break;
				}
			for(i = 0, Betas[2] = 0; i < 6; i++) if(EXPB2_SF[i] && abs(EXPB2_SF[i]) != Alphas[2])
				{
				Betas[2] = EXPB2_SF[i] % Alphas[2];
				if(Betas[2] < 0) Betas[2] += Alphas[2];
				break;
				}
			for(i = 0, F1  = TRUE; i < 6; i++)
				{
				if(abs(EXPA2_SF[i]) == Alphas[1])
					{
					F1 = FALSE;
					break;
					}
				if(abs(EXPB2_SF[i]) == Alphas[2])
					{
					F1 = FALSE;
					break;
					}	
				}
			if(F1 == TRUE)
				{
				for(i = 0, Alphas[3] = 0; i < 6; i++) Alphas[3] += NEXA2_SF[i];
				
				/*********************************************************************************
					If both generators appear in the SF relator Relators[1] with exponents of 
					the same sign, Betas[2] needs to be replaced by -Betas[2] mod Alphas[2].
				*********************************************************************************/
				
				if(EXPA1_SF[0]*EXPB1_SF[0] > 0) Betas[2] = Alphas[2] - Betas[2];
				return(0);
				}
				
			/*** Check if an 'A' exponent has absolute value > 2 in R1 or R2. ***/
			
			if(Alphas[1] > 2)
				FA = TRUE;
			else for(i = 0, FA  = FALSE; i < 6; i++)
				{
				if(abs(EXPA2_SF[i]) > 2)
					{
					FA = TRUE;
					break;
					}
				}
				
			if(FA)
				{
				for(i = MA = 0; i < 6; i++)
					{
					j = abs(EXPA2_SF[i]);
					if(j && j != Alphas[1] && j > MA) MA = j;
					}
				if(MA == 0)
					{
					Alphas[3] = 0;
					return(0);					
					}	
				for(i = NA = 0; i < 6; i++)
					{
					j = abs(EXPA2_SF[i]);
					if(j && j != Alphas[1] && j != MA)
						{
						NA = j;
						break;
						}
					}
				if(NA == 0)
					{
					for(i = Alp3A = 0; i < 6; i++)
						{
						j = EXPA2_SF[i];
						if(j ==  MA) Alp3A += NEXA2_SF[i];
						if(j == -MA) Alp3A -= NEXA2_SF[i];
						}		
					}
				if(NA && (MA < Alphas[1]))
					{
					for(i = Alp3A = 0; i < 6; i++)
						{
						j = EXPA2_SF[i];
						if(j ==  MA) Alp3A += NEXA2_SF[i];
						if(j == -MA) Alp3A -= NEXA2_SF[i];
						if(j ==  NA) Alp3A -= NEXA2_SF[i];
						if(j == -NA) Alp3A += NEXA2_SF[i];
						}							
					}
				if(NA && (MA > Alphas[1]))
					{
					for(i = Alp3A = 0; i < 6; i++)
						{
						j = EXPA2_SF[i];
						if(j ==  MA) Alp3A += NEXA2_SF[i];
						if(j == -MA) Alp3A -= NEXA2_SF[i];
						if(j ==  NA) Alp3A += NEXA2_SF[i];
						if(j == -NA) Alp3A -= NEXA2_SF[i];
						}							
					}
				Alphas[3] = abs(Alp3A);					
				}	
				
			/*** Check if a 'B' exponent has absolute value > 2 in R1 or R2. ***/
			
			if(Alphas[2] > 2)
				FB = TRUE;
			else for(i = 0, FB  = FALSE; i < 6; i++)
				{
				if(abs(EXPB2_SF[i]) > 2)
					{
					FB = TRUE;
					break;
					}
				}
				
			if(FB)
				{
				for(i = MB = 0; i < 6; i++)
					{
					j = abs(EXPB2_SF[i]);
					if(j && j != Alphas[2] && j > MB) MB = j;
					}
				if(MB == 0)
					{
					Alphas[3] = 0;
					return(0);					
					}	
				for(i = NB = 0; i < 6; i++)
					{
					j = abs(EXPB2_SF[i]);
					if(j && j != Alphas[2] && j != MB)
						{
						NB = j;
						break;
						}
					}
				if(NB == 0)
					{
					for(i = Alp3B = 0; i < 6; i++)
						{
						j = EXPB2_SF[i];
						if(j ==  MB) Alp3B += NEXB2_SF[i];
						if(j == -MB) Alp3B -= NEXB2_SF[i];
						}		
					}
				if(NB && (MB < Alphas[2]))
					{
					for(i = Alp3B = 0; i < 6; i++)
						{
						j = EXPB2_SF[i];
						if(j ==  MB) Alp3B += NEXB2_SF[i];
						if(j == -MB) Alp3B -= NEXB2_SF[i];
						if(j ==  NB) Alp3B -= NEXB2_SF[i];
						if(j == -NB) Alp3B += NEXB2_SF[i];
						}							
					}
				if(NB && (MB > Alphas[2]))
					{
					for(i = Alp3B = 0; i < 6; i++)
						{
						j = EXPB2_SF[i];
						if(j ==  MB) Alp3B += NEXB2_SF[i];
						if(j == -MB) Alp3B -= NEXB2_SF[i];
						if(j ==  NB) Alp3B += NEXB2_SF[i];
						if(j == -NB) Alp3B -= NEXB2_SF[i];
						}							
					}
				Alphas[3] = abs(Alp3B);
				}
			
			if(Alphas[1] > 2 && Alphas[2] > 2)
				{
				Betas[1] = MA % Alphas[1];
				Betas[2] = MB % Alphas[2];
							
				/*********************************************************************************
					If both generators appear in the SF relator Relators[1] with exponents of 
					identical (resp different) signs and ALp3A and Alp3B also have identical 
					(resp different) signs, Betas[2] needs to be replaced by -Betas[2] mod 
					Alphas[2]. 		
				*********************************************************************************/
				
				if(EXPA1_SF[0]*EXPB1_SF[0] > 0 && Alp3A*Alp3B > 0) Betas[2] = Alphas[2] - Betas[2];
				if(EXPA1_SF[0]*EXPB1_SF[0] < 0 && Alp3A*Alp3B < 0) Betas[2] = Alphas[2] - Betas[2];
				
				}
						
			if(FA || FB) return(0);
					
			/*** Neither generator appears in R1 or R2 with exponents greater than 2! ***/
							
			Get_SF_Alphas2(1);					
			}
		}
		
	if(Num == 2)
		{
		for(i = 0, Alphas[1] = 0; i < 3; i++) Alphas[1] += NEXA1_SF[i]*(abs(EXPA1_SF[i]));
		Alphas[2] = abs(EXPB1_SF[0]);
		if(NumRelators == 1) return(0);
		if(NumRelators == 2)
			{
			for(i = 0, Betas[1] = 0; i < 3; i++) Betas[1] += NEXA1_SF[i];		
			Get_SF_Alphas2(2);
			}					
		}
	if(Num == 3)
		{
		for(i = 0, Alphas[2] = 0; i < 3; i++) Alphas[2] += NEXB1_SF[i]*(abs(EXPB1_SF[i]));
		Alphas[1] = abs(EXPA1_SF[0]);
		if(NumRelators == 1) return(0);
		if(NumRelators == 2)
			{
			for(i = 0, Betas[2] = 0; i < 3; i++) Betas[2] += NEXB1_SF[i];
			Get_SF_Alphas2(3);
			}					
		}				
	return(0);
}

int Get_SF_Invariants(int OrbitNum,char F1)
{
int			A1,
			A2,
			B1,
			B2,
			H1,
			i,
			j,
			k,
			n,
			NumSolns,
			PSum1,
			PSum2,
			PSum3,
			SolV[7],
			SumAR1,
			SumBR1,
			SumAR2,
			SumBR2;
	
	if(Batch == FALSE)
		{
		if(F1 == 0)
			{
			i = OrbitNum - 1;		
			printf("\n\nPresentation %d  of Summand %u:  Gen  %d  Rel  %d  Length  %lu  From Pres %u. \n",
				i+1,ComponentNum[i],NG[i],NR[i],SURL[i],FR[i]+1);
			Print_Relators(SUR[i],NR[i]);	
			printf("\n\npresents:");		
			}	
		if(F1 == 1) printf("\n\nThe Manifolds of Orbit %4d are:", OrbitNum);
		if(F1 == 2) printf("\n\nThe manifold H'[R] is");
		}	

	if(NumRelators == 1)
		{
		A1 = Alphas[1];
		A2 = Alphas[2];
		if(A1 > A2)
			{
			i = A1;
			A1 = A2;
			A2 = i;
			}
		FoundSF = TRUE;
		if(F1 == 3) return(1);			
		if(F1 == 2) printf(" SF D(%d,%d)",A1,A2);
		else printf(" SF(0;m/%d,n/%d), 0 < m < %d, 0 < n < %d, gcd(m,%d) = gcd(n,%d) = 1.",
		A1,A2,A1,A2,A1,A2);
		if(B10B11Recognized)
			{
			SFSolV[0] = 7;			
			SFSolV[5] = A1;
			SFSolV[7] = A2;
			}
		return(1);
		}
			
	if(Alphas[1] == 0 || Alphas[2] == 0) return(TOO_LONG);

	if(Alphas[3] == 0)
		{
		A1 = Alphas[1];
		A2 = Alphas[2];
		B1 = Betas[1];
		B2 = Betas[2];
		if(B1) B1 = Recip_Mod_P(A1,B1);
		if(B2) B2 = Recip_Mod_P(A2,B2);
		if(A1 > A2 || (A1 == A2 && B1 > B2))
			{
			i = A1;
			A1 = A2;
			A2 = i;
			j = B1;
			B1 = B2;
			B2 = j;
			}
		switch(A1)
			{
			case 1: 
				B1 = 0;
				break;
			case 2:
			case 3:
			case 4:
			case 6:	
				B1 = 1;
				break;	
			}
		switch(A2)
			{
			case 1: 
				B2 = 0;
				break;
			case 2:
			case 3:
			case 4:
			case 6:	
				B2 = 1;
				break;				
			}		
		if(B1 == 0 && B2 == 0)
			{
			FoundSF = TRUE;
			printf(" Connected sums of lens spaces: L(%d,Q_1) # L(%d,Q_2).",A1,A2);
			if(B10B11Recognized)
				{
				SFSolV[0] = 8;			
				SFSolV[5] = A1;
				SFSolV[7] = A2;
				}			
			return(2);
			}
		if(B1 == 0)
			{
			FoundSF = TRUE;
			printf(" Connected sums of lens spaces: L(%d,Q) # L(%d,%d).",A1,A2,B2);
			if(B10B11Recognized)
				{
				SFSolV[0] = 9;			
				SFSolV[5] = A1;
				SFSolV[6] = B2;
				SFSolV[7] = A2;
				}			
			return(2);
			}
		if(B2 == 0)
			{
			FoundSF = TRUE;
			printf(" Connected sums of lens spaces: L(%d,%d) # L(%d,Q).",A1,B1,A2);
			if(B10B11Recognized)
				{
				SFSolV[0] = 10;
				SFSolV[4] = B1;			
				SFSolV[5] = A1;
				SFSolV[6] = B2;
				SFSolV[7] = A2;
				}					
			return(2);
			}
		FoundSF = TRUE;	
		printf(" Connected sums of lens spaces: L(%d,%d) # L(%d,%d).",A1,B1,A2,B2);
		if(B10B11Recognized)
			{
			SFSolV[0] = 11;
			SFSolV[4] = B1;			
			SFSolV[5] = A1;
			SFSolV[6] = B2;
			SFSolV[7] = A2;
			}				
		return(2);
		}
		
	for(i = 0, SumAR1 = 0; i < 3; i++)	SumAR1 += NEXA1_SF[i]*EXPA1_SF[i];
	for(i = 0, SumBR1 = 0; i < 3; i++)	SumBR1 += NEXB1_SF[i]*EXPB1_SF[i];
	for(i = 0, SumAR2 = 0; i < 6; i++)	SumAR2 += NEXA2_SF[i]*EXPA2_SF[i];
	for(i = 0, SumBR2 = 0; i < 6; i++)	SumBR2 += NEXB2_SF[i]*EXPB2_SF[i];
		
	H1 = abs(SumAR1*SumBR2-SumAR2*SumBR1);
	
	/*** If Alphas[3] = 1, we have a lens space. ***/
	
	NumSolns = 0;	
	PSum1 = Betas[1]*Alphas[2]*Alphas[3]+Alphas[1]*Betas[2]*Alphas[3];
	PSum2 = H1-PSum1;
	j = Alphas[1]*Alphas[2];
	k = PSum2 % j;
	if(k == 0)
		{
		PSum3 = PSum2/j;
		Betas[3] = PSum3 % Alphas[3];
		if(Betas[3] < 0) Betas[3] = Betas[3] + Alphas[3];
		PSum3 -= Betas[3];	
		n = PSum3/Alphas[3];
		n = -n;	
		if(GCD(Alphas[3],Betas[3]) == 1) 
			{
			SF_Sort_And_Print(H1,n,Alphas[1],Alphas[2],Alphas[3],Betas[1],Betas[2],Betas[3],NumSolns,SolV);		
			NumSolns ++;
			}
		}
		
	if(Alphas[1] > 2 || Alphas[2] > 2)
		{
		PSum1 = (Alphas[1]-Betas[1])*Alphas[2]*Alphas[3]+Alphas[1]*(Alphas[2]-Betas[2])*Alphas[3];
		PSum2 = H1-PSum1;
		j = Alphas[1]*Alphas[2];
		k = PSum2 % j;
		if(k == 0)
			{
			PSum3 = PSum2/j;
			Betas[3] = PSum3 % Alphas[3];
			if(Betas[3] < 0) Betas[3] = Betas[3] + Alphas[3];
			PSum3 -= Betas[3];
			n = PSum3/Alphas[3];
			n = -n;	
			if(H1 && (GCD(Alphas[3],Betas[3]) == 1))
				{
				if(SF_Sort_And_Print(H1,n,Alphas[1],Alphas[2],Alphas[3],Alphas[1]-Betas[1],Alphas[2]-Betas[2],Betas[3],NumSolns,SolV))
				NumSolns ++;
				}
			}
		}
		
if(NumSolns == 2) return(5);			
return(0);		
}

int Get_SF_Alphas2(int Num)
{
    /******************************************************************************************
   		The routine Get_SF_Alphas1() can easily determine the values of Alphas 1, 2 and 3
   	when each generator appears in the relators with an exponent of absolute value greater 
   	than 2.
   		The routine Get_SF_Alphas2() is used in the remaining cases when a generator appears
   	appears only with exponents of absolute value less than 3.
    ******************************************************************************************/    
    
    char		*p,
				*q,
    			**Rel = NULL,
    			Sign;
    						
    unsigned char  	x,
					y;

                            
    int			i,
	   			AExpP,
    			AExpQ,
    			AExpR,
    			BExpS,
    			BExpT,
    			BExpU,
    			ex,
    			j,
    			Mex,
				sex;
		
    p = (char *)*Relators[2];
	x = *p++;
	if(!x) return(2);			/* Relators[2] is empty!  */
	
	Rel = (char **) NewHandle(GetHandleSize((char **) Relators[2]));
	if(Rel == NULL) Mem_Error();
	q = *Rel;
	
	if(Num == 2)
		{
		for(i = 0, Mex = 0; i < 3; i++) if(abs(EXPA1_SF[i]) > Mex) Mex = abs(EXPA1_SF[i]);
		Mex--;
		for(i = 0, BExpS = Alphas[2], BExpT = BExpU = 0; i < 6; i++)
			{
			j = abs(EXPB2_SF[i]);
			if(j == 0 || j == BExpS) continue;
			if(j == BExpT) continue;
			if(BExpT == 0) 
				{
				BExpT = j;
				continue;
				}
			if(j == BExpU) continue;
			if(BExpU == 0) BExpU = j;
			}
		}
	if(Num == 3)
		{
		for(i = 0, Mex = 0; i < 3; i++) if(abs(EXPB1_SF[i]) > Mex) Mex = abs(EXPB1_SF[i]);
		Mex--;
		for(i = 0, AExpP = Alphas[1], AExpQ = AExpR = 0; i < 6; i++)
			{
			j = abs(EXPA2_SF[i]);
			if(j == 0 || j == AExpP) continue;
			if(j == AExpQ) continue;
			if(AExpQ == 0) 
				{
				AExpQ = j;
				continue;
				}
			if(j == AExpR) continue;
			if(AExpR == 0) AExpR = j;
			}
		}
				
	ex = 1;
	while(*p == x)
		{
		ex++;
		p++;
		}
	sex = ex;
	ex = 0;
	if(*p) x = *p;
	while( (y = *p++) )
		{
		if(x == y)
			ex++;
		else
			{
			if(Num == 1)
				{
				if(abs(ex) == 1) *q++ = x;
				if(ex == 2)
					{
					if(x == 'A') *q++ = 'C';
					if(x == 'a') *q++ = 'c';					
					if(x == 'B') *q++ = 'D';
					if(x == 'b') *q++ = 'd';
					}
				}
			if(Num == 2)
				{
				if(x == 'A')
					{
					if(ex == Mex) *q++ = 'c';
					else *q++ = 'C';
					}
				if(x == 'a')
					{
					if(ex == Mex) *q++ = 'C';
					else *q++ = 'c';
					}
				if(x == 'B')
					{
					if(ex == BExpS) *q++ = 'S';
					if(ex == BExpT) *q++ = 'T';
					if(ex == BExpU) *q++ = 'U';
					}
				if(x == 'b')
					{
					if(ex == BExpS) *q++ = 's';
					if(ex == BExpT) *q++ = 't';
					if(ex == BExpU) *q++ = 'u';
					}								
				}
			if(Num == 3)
				{
				if(x == 'A')
					{
					if(ex == AExpP) *q++ = 'P';
					if(ex == AExpQ) *q++ = 'Q';
					if(ex == AExpR) *q++ = 'R';
					}
				if(x == 'a')
					{
					if(ex == AExpP) *q++ = 'p';
					if(ex == AExpQ) *q++ = 'q';
					if(ex == AExpR) *q++ = 'r';
					}								
				if(x == 'B')
					{
					if(ex == Mex) *q++ = 'd';
					else *q++ = 'D';
					}
				if(x == 'b')
					{
					if(ex == Mex) *q++ = 'D';
					else *q++ = 'd';
					}	
				}						

			ex = 1;    
			}
		x = y;
		}
	y = **Relators[2];        
	if(x == y)
		{
		ex += sex;	
		if(Num == 1)
			{
			if(abs(ex) == 1) *q++ = x;
			if(ex == 2)
				{
				if(x == 'A') *q++ = 'C';
				if(x == 'a') *q++ = 'c';					
				if(x == 'B') *q++ = 'D';
				if(x == 'b') *q++ = 'd';
				}
			}
		if(Num == 2)
			{
			if(x == 'A')
				{
				if(ex == Mex) *q++ = 'c';
				else *q++ = 'C';
				}
			if(x == 'a')
				{
				if(ex == Mex) *q++ = 'C';
				else *q++ = 'c';
				}
			if(x == 'B')
				{
				if(ex == BExpS) *q++ = 'S';
				if(ex == BExpT) *q++ = 'T';
				if(ex == BExpU) *q++ = 'U';
				}
			if(x == 'b')
				{
				if(ex == BExpS) *q++ = 's';
				if(ex == BExpT) *q++ = 't';
				if(ex == BExpU) *q++ = 'u';
				}									
			}
		if(Num == 3)
			{
			if(x == 'A')
				{
				if(ex == AExpP) *q++ = 'P';
				if(ex == AExpQ) *q++ = 'Q';
				if(ex == AExpR) *q++ = 'R';
				}
			if(x == 'a')
				{
				if(ex == AExpP) *q++ = 'p';
				if(ex == AExpQ) *q++ = 'q';
				if(ex == AExpR) *q++ = 'r';
				}												
			if(x == 'B')
				{
				if(ex == Mex) *q++ = 'd';
				else *q++ = 'D';
				}
			if(x == 'b')
				{
				if(ex == Mex) *q++ = 'D';
				else *q++ = 'd';
				}	
			}												
		}
	else
		{
		if(Num == 1)
			{
			if(abs(ex) == 1) *q++ = x;
			if(ex == 2)
				{
				if(x == 'A') *q++ = 'C';
				if(x == 'a') *q++ = 'c';					
				if(x == 'B') *q++ = 'D';
				if(x == 'b') *q++ = 'd';
				}
			}
		if(Num == 2)
			{
			if(x == 'A')
				{
				if(ex == Mex) *q++ = 'c';
				else *q++ = 'C';
				}
			if(x == 'a')
				{
				if(ex == Mex) *q++ = 'C';
				else *q++ = 'c';
				}
			if(x == 'B')
				{
				if(ex == BExpS) *q++ = 'S';
				if(ex == BExpT) *q++ = 'T';
				if(ex == BExpU) *q++ = 'U';
				}
			if(x == 'b')
				{
				if(ex == BExpS) *q++ = 's';
				if(ex == BExpT) *q++ = 't';
				if(ex == BExpU) *q++ = 'u';
				}												
			}
		if(Num == 3)
			{
			if(x == 'A')
				{
				if(ex == AExpP) *q++ = 'P';
				if(ex == AExpQ) *q++ = 'Q';
				if(ex == AExpR) *q++ = 'R';
				}
			if(x == 'a')
				{
				if(ex == AExpP) *q++ = 'p';
				if(ex == AExpQ) *q++ = 'q';
				if(ex == AExpR) *q++ = 'r';
				}							
			if(x == 'B')
				{
				if(ex == Mex) *q++ = 'd';
				else *q++ = 'D';
				}
			if(x == 'b')
				{
				if(ex == Mex) *q++ = 'D';
				else *q++ = 'd';
				}	
			}					
		
		ex = sex;
		x = y;
		
		if(Num == 1)
			{
			if(abs(ex) == 1) *q++ = x;
			if(ex == 2)
				{
				if(x == 'A') *q++ = 'C';
				if(x == 'a') *q++ = 'c';					
				if(x == 'B') *q++ = 'D';
				if(x == 'b') *q++ = 'd';
				}
			}
		if(Num == 2)
			{
			if(x == 'A')
				{
				if(ex == Mex) *q++ = 'c';
				else *q++ = 'C';
				}
			if(x == 'a')
				{
				if(ex == Mex) *q++ = 'C';
				else *q++ = 'c';
				}
			if(x == 'B')
				{
				if(ex == BExpS) *q++ = 'S';
				if(ex == BExpT) *q++ = 'T';
				if(ex == BExpU) *q++ = 'U';
				}
			if(x == 'b')
				{
				if(ex == BExpS) *q++ = 's';
				if(ex == BExpT) *q++ = 't';
				if(ex == BExpU) *q++ = 'u';
				}									
			}
		if(Num == 3)
			{
			if(x == 'A')
				{
				if(ex == AExpP) *q++ = 'P';
				if(ex == AExpQ) *q++ = 'Q';
				if(ex == AExpR) *q++ = 'R';
				}
			if(x == 'a')
				{
				if(ex == AExpP) *q++ = 'p';
				if(ex == AExpQ) *q++ = 'q';
				if(ex == AExpR) *q++ = 'r';
				}						
			if(x == 'B')
				{
				if(ex == Mex) *q++ = 'd';
				else *q++ = 'D';
				}
			if(x == 'b')
				{
				if(ex == Mex) *q++ = 'D';
				else *q++ = 'd';
				}	
			}								
		}
		
    *q = EOS;
    
    if(Num == 1)
    	{
    	for(p = *Rel,Sign = 1,ex = 0; *p; p++)
    		{
    		if(*p == 'A' || *p == 'a')
    			{
    			if(Sign > 0) ex++;
    			if(Sign < 0) ex--;
    			}
    		if(*p == 'C' || *p == 'c' || *p == 'D' || *p == 'd') Sign = -Sign;	
    		}	
    	Alphas[3] = abs(ex);
    	}
    
    if(Num == 2)
    	{
    	for(p = *Rel, q = p + 1, ex = 0; *p && *q; p++, q++) 
    	if(*p == 'T' || *p == 'U' || *p == 't' || *p == 'u')
    		{
    		if(*q == 'C') ex++;
    		if(*q == 'c') ex--;
    		}
    	q = *Rel;
    	if(*p == 'T' || *p == 'U' || *p == 't' || *p == 'u')
    		{
    		if(*q == 'C') ex++;
    		if(*q == 'c') ex--;
    		}
    	Alphas[3] = abs(ex);	
    	}
    if(Num == 3)
    	{
    	for(p = *Rel, q = p + 1, ex = 0; *p && *q; p++, q++) 
    	if(*p == 'Q' || *p == 'R' || *p == 'q' || *p == 'r')
    		{
    		if(*q == 'D') ex++;
    		if(*q == 'd') ex--;
    		}
    	q = *Rel;
    	if(*p == 'Q' || *p == 'R' || *p == 'q' || *p == 'r')
    		{
    		if(*q == 'D') ex++;
    		if(*q == 'd') ex--;
    		}
    	Alphas[3] = abs(ex);	
    	}    	
 	
 	if(Num == 2 && Alphas[2] > 2) 		/*** Set Betas[2]  ***/
 		{
 		for(p = *Rel, q = p + 1; *p && *q; p++, q++)
 			{
 			if(*p == 'C')
 				{
 				if(*q == 'S' || *q == 's') continue;
 				if(*q == EOS) q = *Rel;
 				if(*q == 'T') j =  BExpT;
 				if(*q == 'U') j =  BExpU; 
 				if(*q == 't') j = -BExpT;
 				if(*q == 'u') j = -BExpU; 
 				}
 			if(*p == 'c')
 				{
 				if(*q == 'S' || *q == 's') continue;
 				if(*q == EOS) q = *Rel;
 				if(*q == 'T') j = -BExpT;
 				if(*q == 'U') j = -BExpU;
 				if(*q == 't') j =  BExpT;
 				if(*q == 'u') j =  BExpU;
 				}	
 			}
 		
 		j = j % Alphas[2];
 		if(j < 0) j += Alphas[2];
 		if(EXPA1_SF[0]*EXPB1_SF[0] > 0) j = Alphas[2] - j;
 		Betas[2] = j;
 		}
 	if(Alphas[2] == 2) Betas[2] = 1;	
 	
 	if(Num == 3 && Alphas[1] > 2) 		/*** Set Betas[1]  ***/
 		{
 		for(p = *Rel, q = p + 1; *p && *q; p++, q++)
 			{
 			if(*p == 'D')
 				{
 				if(*q == 'P' || *q == 'p') continue;
 				if(*q == EOS) q = *Rel;
 				if(*q == 'Q') j =  AExpQ;
 				if(*q == 'R') j =  AExpR; 
 				if(*q == 'q') j = -AExpQ;
 				if(*q == 'r') j = -AExpR; 
 				}
 			if(*p == 'd')
 				{
 				if(*q == 'P' || *q == 'p') continue;
 				if(*q == EOS) q = *Rel;
 				if(*q == 'Q') j = -AExpQ;
 				if(*q == 'R') j = -AExpR;
 				if(*q == 'q') j =  AExpQ;
 				if(*q == 'r') j =  AExpR;
 				}	
 			}
 		
 		j = j % Alphas[1];
 		if(j < 0) j += Alphas[1];
 		if(EXPA1_SF[0]*EXPB1_SF[0] > 0) j = Alphas[1] - j;
 		Betas[1] = j;
 		}
 	if(Alphas[1] == 2) Betas[1] = 1;			
 
    if(Rel != NULL)
    	{
    	DisposeHandle((char **) Rel);
    	Rel = NULL;
    	}
    return(0);            
}

int SF_Sort_And_Print(int H1, int n, int A1, int A2, int A3, int B1, int B2, int B3, int NumSolns, int* SolV)
{
	char	Finite;

	int		i,
			Q,
			R;

		if(A3 == 1)		/*** We have a lens space. ***/
			{
			i = n*A1 - B1;
			Q = GCD(A1,abs(i));
			if(i < 0)
				Q = A2*Recip_P-B2*Recip_Q;
			else
				Q = A2*Recip_P+B2*Recip_Q;			
			if(Q < 0) Q = -Q;
			if(H1 == 0)
				{
				FoundSF = TRUE;
				printf(" S1 X S2");
				if(B10B11Recognized) 
					{
					SFSolV[0] = 12;
					SFSolV[4] = 1;			
					SFSolV[5] = 0;
					}				
				return(0);
				}
			Q = Q % H1;	
			R = H1 - Q;
			GCD(H1,Q);
			if(labs(Recip_Q) < Q) Q = labs(Recip_Q);
			GCD(H1,R);
			if(labs(Recip_Q) < R) R = labs(Recip_Q);
			if(R < Q) Q = R;
			}

		if(A1 > A2)
			{
			i = A1;
			A1 = A2;
			A2 = i;
			i = B1;
			B1 = B2;
			B2 = i;				
			}
		if(A2 > A3)
			{
			i = A2;
			A2 = A3;
			A3 = i;
			i = B2;
			B2 = B3;
			B3 = i;				
			}
		if(A1 > A2)
			{
			i = A1;
			A1 = A2;
			A2 = i;
			i = B1;
			B1 = B2;
			B2 = i;				
			}
		if(A1 == A2 && B1 > B2)
			{
			i = B1;
			B1 = B2;
			B2 = i;
			}
		if(A2 == A3 && B2 > B3)
			{
			i =  B2;
			B2 = B3;
			B3 = i;
			}
		if(A1 == A2 && B1 > B2)
			{
			i = B1;
			B1 = B2;
			B2 = i;
			}
		if(Alphas[3] == 1)  /*** We have a lens space. ***/
			{
			if(H1 == 0)
				{
				FoundSF = TRUE;
				printf(" S1 X S2");
				if(B10B11Recognized) 
					{
					SFSolV[0] = 13;
					SFSolV[4] = 1;			
					SFSolV[5] = 0;
					}				
				}
			else
				{
				FoundSF = TRUE;
				FoundFiniteSF = TRUE;
				printf(" Lens spaces: SF(0;%d;%d/%d,%d/%d) = L(%d,%d)",n,B2,A2,B3,A3,H1,Q);
				if(B10B11Finite || B10B11Recognized) 
					{
					SFSolV[0] = 14;
					SFSolV[6] = B2;
					SFSolV[7] = A2;
					SFSolV[8] = B3;
					SFSolV[9] = A3;
					SFSolV[10] = n;
					SFSolV[18] = H1;
					SFSolV[19] = Q;
					}				
				}
			}
		else
			{	
			if(NumSolns == 0)
				{
				SolV[0] = n;
				SolV[1] = B1;
				SolV[2] = A1;
				SolV[3] = B2;
				SolV[4] = A2;
				SolV[5] = B3;
				SolV[6] = A3;
				FoundSF = TRUE;
				printf(" SF(0;%d;%d/%d,%d/%d,%d/%d) or OR",n,B1,A1,B2,A2,B3,A3);
				printf(" SF(0;%d;%d/%d,%d/%d,%d/%d)",3-n,A1-B1,A1,A2-B2,A2,A3-B3,A3);
				if(B10B11Recognized)
					{
					SFSolV[0] = 15;
					SFSolV[4] = B1;
					SFSolV[5] = A1;
					SFSolV[6] = B2;
					SFSolV[7] = A2;
					SFSolV[8] = B3;
					SFSolV[9] = A3;
					SFSolV[10] = n;
					}					
				Finite = FALSE;	
				if(A1 == 2)
					{
					switch(A2)
						{
						case 2:
							Finite = TRUE;
							printf(" Finite!");
							break;
						case 3:
							switch(A3)
								{
								case 3:
								case 4:
								case 5:
									Finite = TRUE;
									printf(" Finite!");
									break;
								default:
									break;	
								}
						default:
							break;
						}			
					}
				if(Finite) FoundFiniteSF = TRUE;	
				if(Finite && B10B11Finite) 
					{
					SFSolV[0] = 16;
					SFSolV[4] = B1;
					SFSolV[5] = A1;
					SFSolV[6] = B2;
					SFSolV[7] = A2;
					SFSolV[8] = B3;
					SFSolV[9] = A3;
					SFSolV[10] = n;
					}								
				}						
			else
				{
				if(SolV[0] != n || SolV[1] != B1 || SolV[2] != A1 || SolV[3] != B2 || SolV[4] != A2 || SolV[5] != B3 || SolV[6] != A3 )
					{
					FoundSF = TRUE;
					printf("\n                     or perhaps:");			
					printf(" SF(0;%d;%d/%d,%d/%d,%d/%d) or OR",n,B1,A1,B2,A2,B3,A3);
					printf(" SF(0;%d;%d/%d,%d/%d,%d/%d)",3-n,A1-B1,A1,A2-B2,A2,A3-B3,A3);
					if(B10B11Recognized)
						{
						SFSolV[0] = 17;
						SFSolV[11] = B1;
						SFSolV[12] = A1;
						SFSolV[13] = B2;
						SFSolV[14] = A2;
						SFSolV[15] = B3;
						SFSolV[16] = A3;
						SFSolV[17] = n;
						}								
					Finite = FALSE;	
					if(A1 == 2)
						{
						switch(A2)
							{
							case 2:
								Finite = TRUE;
								printf(" Finite!");
								break;
							case 3:
								switch(A3)
									{
									case 3:
									case 4:
									case 5:
										Finite = TRUE;
										printf(" Finite!");
										break;
									default:
										break;	
									}
							default:
								break;
							}			
						}
					if(Finite) FoundFiniteSF = TRUE;	
					if(Finite && B10B11Finite)
						{
						SFSolV[0] = 18;
						SFSolV[11] = B1;
						SFSolV[12] = A1;
						SFSolV[13] = B2;
						SFSolV[14] = A2;
						SFSolV[15] = B3;
						SFSolV[16] = A3;
						SFSolV[17] = n;
						}							
					return(1);
					}
				}
			}
	return(0);
}

void Test_Transverse(void)
{
	unsigned char	*ptr = NULL;

	unsigned int	Whitehead_Graph();

	NumGenerators = 2;
	NumRelators   = 2;
	Vertices      = 4;
	
	if(Find_Flow_A(NORMAL,FALSE)) return;
	
	Whitehead_Graph();
	
	ptr = (unsigned char*) NewPtr(500);
	if(ptr == NULL) Mem_Error();
	Transverse(ptr);
	
	Print_Relators(Relators,NumRelators);
	printf("\n %s",ptr);
	DisposePtr((char*) ptr);	
}	

int Init_Genus_Two_Essential_Tori(int* MyTable,int MyStart,int MyCompNum,char F1)
{
	unsigned char	*p,
					*q;
					
	int				i,
					n,
					NumPresChecked;

	/****** Check which genus two presentations have essential tori. ******/	

	for(n = MyStart,NumPresChecked = 0; n >= 0; n--) 
		{
		ReadPres 		= MyTable[n];
		if(CS[ComponentNum[ReadPres]] == 1) continue;
		if(ComponentNum[ReadPres] >  MyCompNum) continue;
		if(ComponentNum[ReadPres] <  MyCompNum) return(n);
		NumGenerators 	= NG[ReadPres];
		NumRelators 	= NR[ReadPres];
		if(NumGenerators != 2) continue;
		if(NumRelators > 2) continue;
		Vertices		= 2*NumGenerators;
		Length 			= SURL[ReadPres];
	    for(i = 1; i <= NumRelators; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(Relators[i] == NULL) Mem_Error();
			q = *Relators[i];    
			p = *SUR[ReadPres][i];
			while( (*q++ = *p++) ) ;
			}
		NumPresChecked ++;
/*		if(!F1 && NumPresChecked > 100) return(n);
		if( F1 && NumPresChecked > 500) return(n);					*/
		i = Genus_Two_Essential_Tori(ReadPres + 1,MyCompNum,F1);
		if(i == 2) FoundEssentialTorus = TRUE;
		if(i) return(n);
		}
	return(n);		
}

int Genus_Two_Essential_Tori(int OrbitNum,int MyCompNum,char F1)
{
	char			FET = FALSE,
					FPT = FALSE,
					F3;
			
	int				i,
					j,
					MAExp,
					MBExp;
	
	unsigned int	KorLP1,
					KorLP2;
	
	int 	CheckForAltExpSigns(char,char),
			GetAlpha2(char,char),
			GetAlpha2Sub1(char,char),
			GetAlpha2Sub2(char,char),
		 	Get2BKorLPs(char,char,unsigned int*,unsigned int*);
	
	Get_Genus_2_EXPS();
	if(NEXA1_SF[6] || NEXB1_SF[6]) return(0);
	if(NumRelators == 2 && (NEXA2_SF[6] || NEXB2_SF[6])) return(0);
	
	for(i = 1; i < 5; i++) Alphas[i] = Betas[i] = 0;
	
	if(NumRelators == 2)
		{
		/* Check whether each generator appears only with exponents ±1 in R1, and if so, check whether R1
			abelianizes to (0,0), (0,±2), or (±2,0). */
	
		F3 = TRUE;
		if(F3 && EXPA1_SF[2] > 0) 		F3 = FALSE;
		if(F3 && EXPB1_SF[2] > 0) 		F3 = FALSE;
		if(F3 && abs(EXPA1_SF[0]) != 1) F3 = FALSE;
		if(F3 && abs(EXPA1_SF[1]) != 1) F3 = FALSE;
		if(F3 && abs(EXPB1_SF[0]) != 1) F3 = FALSE;
		if(F3 && abs(EXPB1_SF[1]) != 1) F3 = FALSE;
		if(F3 && NEXA1_SF[0] == NEXA1_SF[1] && NEXB1_SF[0] == NEXB1_SF[1])
			{
			if(!FET && CheckForAltExpSigns(1,'A')) 
				{
				Get2BKorLPs(1,'A',&KorLP1,&KorLP2);
				j = GetAlpha2(2,'A');
				if(j == 0) j = GetAlpha2Sub2(2,'A');
				if(j == 0) j = GetAlpha2Sub1(2,'A');
				if(j == 0) return(0);
				FET = 16; 				
				}
			if(!FET && CheckForAltExpSigns(1,'B'))
				{
				Get2BKorLPs(1,'B',&KorLP1,&KorLP2);
				j = GetAlpha2(2,'B');
				if(j == 0) j = GetAlpha2Sub2(2,'B');
				if(j == 0) j = GetAlpha2Sub1(2,'B');
				if(j == 0) return(0);
				FET = 17;				
				}
			}
		if(F3 && NEXA1_SF[0] == NEXA1_SF[1] && abs(NEXB1_SF[0] - NEXB1_SF[1]) == 2)	
			if(!FET && CheckForAltExpSigns(1,'A'))
				{
				Get2BKorLPs(1,'A',&KorLP1,&KorLP2);
				j = GetAlpha2(2,'A');
				if(j == 0) j = GetAlpha2Sub2(2,'A');
				if(j == 0) j = GetAlpha2Sub1(2,'A');
				if(j == 0) return(0);
				FET = 18;				
				}
		if(F3 && abs(NEXA1_SF[0] - NEXA1_SF[1]) == 2 && NEXB1_SF[0] == NEXB1_SF[1])	
			if(!FET && CheckForAltExpSigns(1,'B'))
				{
				Get2BKorLPs(1,'B',&KorLP1,&KorLP2);
				j = GetAlpha2(2,'B');
				if(j == 0) j = GetAlpha2Sub2(2,'B');
				if(j == 0) j = GetAlpha2Sub1(2,'B');
				if(j == 0) return(0);
				FET = 19;				
				}

		/* Check whether each generator appears only with exponents ±1 in R2, and if so, check whether R2
			abelianizes to (0,0), (0,±2), or (±2,0). */
		
		F3 = TRUE;
		if(F3 && EXPA2_SF[2] > 0) 		F3 = FALSE;
		if(F3 && EXPB2_SF[2] > 0) 		F3 = FALSE;
		if(F3 && abs(EXPA2_SF[0]) != 1) F3 = FALSE;
		if(F3 && abs(EXPA2_SF[1]) != 1) F3 = FALSE;
		if(F3 && abs(EXPB2_SF[0]) != 1) F3 = FALSE;
		if(F3 && abs(EXPB2_SF[1]) != 1) F3 = FALSE;
		if(F3 && NEXA2_SF[0] == NEXA2_SF[1] && NEXB2_SF[0] == NEXB2_SF[1])
			{
			if(!FET && CheckForAltExpSigns(2,'A'))
				{
				Get2BKorLPs(2,'A',&KorLP1,&KorLP2);
				j = GetAlpha2(1,'A');
				if(j == 0) j = GetAlpha2Sub2(1,'A');
				if(j == 0) j = GetAlpha2Sub1(1,'A');
				if(j == 0) return(0);
				FET = 20;				
				}
			if(!FET && CheckForAltExpSigns(2,'B'))
				{
				Get2BKorLPs(2,'B',&KorLP1,&KorLP2);
				j = GetAlpha2(1,'B');
				if(j == 0) j = GetAlpha2Sub2(1,'B');
				if(j == 0) j = GetAlpha2Sub1(1,'B');
				if(j == 0) return(0);
				FET = 21;				
				}
			}
		if(F3 && NEXA2_SF[0] == NEXA2_SF[1] && abs(NEXB2_SF[0] - NEXB2_SF[1]) == 2)	
			if(!FET && CheckForAltExpSigns(2,'A'))
				{
				Get2BKorLPs(2,'A',&KorLP1,&KorLP2);
				j = GetAlpha2(1,'A');
				if(j == 0) j = GetAlpha2Sub2(1,'A');
				if(j == 0) j = GetAlpha2Sub1(1,'A');
				if(j == 0) return(0);			
				FET = 22;				
				}
		if(F3 && abs(NEXA2_SF[0] - NEXA2_SF[1]) == 2 && NEXB2_SF[0] == NEXB2_SF[1])	
			if(!FET && CheckForAltExpSigns(2,'B'))
				{
				Get2BKorLPs(2,'B',&KorLP1,&KorLP2);
				j = GetAlpha2(1,'B');
				if(j == 0) j = GetAlpha2Sub2(1,'B');
				if(j == 0) j = GetAlpha2Sub1(1,'B');
				if(j == 0) return(0);			
				FET = 23;				
				}		
		}
	
	/* Check that each generator appears with exponents having absolute value greater than one. */
	
	for(i = 0, MAExp = 0; i < 6; i++) if(abs(EXPA1_SF[i]) > MAExp) MAExp = abs(EXPA1_SF[i]);
	for(i = 0, MBExp = 0; i < 6; i++) if(abs(EXPB1_SF[i]) > MBExp) MBExp = abs(EXPB1_SF[i]);
	if(NumRelators == 2)
		{
		for(i = 0; i < 6; i++) if(abs(EXPA2_SF[i]) > MAExp) MAExp = abs(EXPA2_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB2_SF[i]) > MBExp) MBExp = abs(EXPB2_SF[i]);		
		}
	if(MAExp == 1 || MBExp == 1) return(0);	
	
	if(abs(EXPA1_SF[0]) > 1)
		{
		if(EXPA1_SF[1] == 0) FPT += 1;
		if(EXPA1_SF[1] == -EXPA1_SF[0] && EXPA1_SF[2] == 0) FPT += 1;
		if(FPT == 1) Alphas[1] = abs(EXPA1_SF[0]);
		}
	if(abs(EXPB1_SF[0]) > 1)
		{
		if(EXPB1_SF[1] == 0) FPT += 2;
		if(EXPB1_SF[1] == -EXPB1_SF[0] && EXPB1_SF[2] == 0) FPT += 2;
		if(FPT >= 2) Alphas[2] = abs(EXPB1_SF[0]);
		}

	if(NumRelators == 2)
		{	
		if(abs(EXPA2_SF[0]) > 1)
			{
			if(EXPA2_SF[1] == 0) FPT += 4;
			if(EXPA2_SF[1] == -EXPA2_SF[0] && EXPA2_SF[2] == 0) FPT += 4;
			if(FPT >= 4) Alphas[3] = abs(EXPA2_SF[0]);
			}
		if(abs(EXPB2_SF[0]) > 1)
			{
			if(EXPB2_SF[1] == 0) FPT += 8;
			if(EXPB2_SF[1] == -EXPB2_SF[0] && EXPB2_SF[2] == 0) FPT += 8;
			if(FPT >= 8) Alphas[4] = abs(EXPB2_SF[0]);
			}
		}
		
	if(FPT || FET) 
		{
		if(FET) FPT = FET;
		switch(FPT)
			{
			case 5:
			case 7:
			case 10:
			case 11:
			case 13:
			case 14:
			case 15:
				return(1);
			}			
		for(i = 1; i < 5; i++) if(Alphas[i]) Genus_Two_Essential_Torus_Betas(i);			
		switch(FPT)
			{
			case 1:
				F3 = TRUE;
				if(abs(NEXA1_SF[0] - NEXA1_SF[1]) > 2) 	F3 = FALSE;
				if(F3 && EXPB1_SF[2] > 0) 				F3 = FALSE;
				if(F3 && abs(EXPB1_SF[0]) != 1) 		F3 = FALSE;
				if(F3 && abs(EXPB1_SF[1]) != 1) 		F3 = FALSE;
				if(F3 && (NEXB1_SF[0] != NEXB1_SF[1])) 	F3 = FALSE;
				if(F3 && CheckForAltExpSigns(1,'B'))
					{
					Get2BKorLPs(1,'B',&KorLP1,&KorLP2);
					j = GetAlpha2(2,'B');
					if(j == 0) j = GetAlpha2Sub2(2,'B');
					if(j == 0) j = GetAlpha2Sub1(2,'B');
					if(j == 0) return(0);
					if(NEXA1_SF[0] == NEXA1_SF[1]) 
						FET = 24;
					else 
						FET = 25;					
					}
				if(FET == 24 || FET == 25) break;	
				if(Betas[1] > 1) FET = 1;
				break;
			case 2:
				F3 = TRUE;
				if(abs(NEXB1_SF[0] - NEXB1_SF[1]) > 2) 	F3 = FALSE;
				if(F3 && EXPA1_SF[2] > 0) 				F3 = FALSE;
				if(F3 && abs(EXPA1_SF[0]) != 1) 		F3 = FALSE;
				if(F3 && abs(EXPA1_SF[1]) != 1) 		F3 = FALSE;
				if(F3 && (NEXA1_SF[0] != NEXA1_SF[1])) 	F3 = FALSE;
				if(F3 && CheckForAltExpSigns(1,'A'))
					{
					Get2BKorLPs(1,'A',&KorLP1,&KorLP2);
					j = GetAlpha2(2,'A');
					if(j == 0) j = GetAlpha2Sub2(2,'A');
					if(j == 0) j = GetAlpha2Sub1(2,'A');
					if(j == 0) return(0);
					if(NEXB1_SF[0] == NEXB1_SF[1])
						FET = 26;
					else
						FET = 27;					
					}
				if(FET == 26 || FET == 27) break;				
				if(Betas[2] > 1) FET = 2;				
				break;
			case 3:
				FET = 3;
				break;							
			case 4:
				F3 = TRUE;
				if(abs(NEXA2_SF[0] - NEXA2_SF[1]) > 2) 	F3 = FALSE;
				if(F3 && EXPB2_SF[2] > 0) 				F3 = FALSE;
				if(F3 && abs(EXPB2_SF[0]) != 1) 		F3 = FALSE;
				if(F3 && abs(EXPB2_SF[1]) != 1) 		F3 = FALSE;
				if(F3 && (NEXB2_SF[0] != NEXB2_SF[1])) 	F3 = FALSE;
				if(F3 && CheckForAltExpSigns(2,'B'))
					{
					Get2BKorLPs(2,'B',&KorLP1,&KorLP2);
					j = GetAlpha2(1,'B');
					if(j == 0) j = GetAlpha2Sub2(1,'B');
					if(j == 0) j = GetAlpha2Sub1(1,'B');
					if(j == 0) return(0);
					if(NEXA2_SF[0] == NEXA2_SF[1])
						FET = 28;
					else
						FET = 29;					
					}
				if(FET == 28 || FET == 29) break;				
				if(Betas[3] > 1) FET = 4;				
				break;
			case 6:
				if((Betas[2] > 1) || Betas[3] > 1) FET = 6;
				break;														
			case 8:
				F3 = TRUE;
				if(abs(NEXB2_SF[0] - NEXB2_SF[1]) > 2) 	F3 = FALSE;
				if(F3 && EXPA2_SF[2] > 0) 				F3 = FALSE;
				if(F3 && abs(EXPA2_SF[0]) != 1) 		F3 = FALSE;
				if(F3 && abs(EXPA2_SF[1]) != 1) 		F3 = FALSE;
				if(F3 && (NEXA2_SF[0] != NEXA2_SF[1])) 	F3 = FALSE;
				if(F3 && CheckForAltExpSigns(2,'A'))
					{
					Get2BKorLPs(2,'A',&KorLP1,&KorLP2);
					j = GetAlpha2(1,'A');
					if(j == 0) j = GetAlpha2Sub2(1,'A');
					if(j == 0) j = GetAlpha2Sub1(1,'A');
					if(j == 0) return(0);
					if(NEXB2_SF[0] == NEXB2_SF[1])
						FET = 30;
					else
						FET = 31;					
					}
				if(FET == 30 || FET == 31) break;				
				if(Betas[4] > 1) FET = 8;				
				break;
			case 9:
				if((Betas[1] > 1) || Betas[4] > 1) FET = 9;
				break;				
			case 12:
				FET = 12;
				break;
			}
		if(FET)
			{
			if(Batch == FALSE)
				{
				if(!F1) printf("\n\n Found an essential torus in the diagram of Orbit %d. ", OrbitNum);
				if(F1)  printf("\n\n Found an essential torus in the diagram of Presentation %d Length %lu. ", OrbitNum,SURL[OrbitNum - 1]);
				}
			if(Batch == 10 || Batch == 11) printf("Has an ET.   ");
			switch(FET)
				{
				case 1:
					printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R1 with A^%d --> A.",Alphas[1],Betas[1],Alphas[1]);
					Stow_ET_Data(MyCompNum,FET,0,Alphas[1],Betas[1],Alphas[1],0,0,0,0,0);
					break;
				case 2:
					printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R1 with B^%d --> B.",Alphas[2],Betas[2],Alphas[2]);
					Stow_ET_Data(MyCompNum,FET,0,Alphas[2],Betas[2],Alphas[2],0,0,0,0,0);
					break;
				case 3:
					i = Betas[1];
					if(Betas[2] > 1) i = Betas[2];
					if(i == 1)
						{
						printf("K3: M = SFD(%d,%d) U 2BK H[R], where R is R1 with A^%d --> A and B^%d --> B.",
						Alphas[1],Alphas[2],Alphas[1],Alphas[2]);
						Stow_ET_Data(MyCompNum,FET,1,Alphas[1],Alphas[2],Alphas[1],Alphas[2],0,0,0,0);
						}
					if(i > 1)
						{
						printf("K3: M = SFD(%d,%d,%d) U 2BK H[R], where R is R1 with A^%d --> A and B^%d --> B.",
						Alphas[1],Alphas[2],i,Alphas[1],Alphas[2]);
						Stow_ET_Data(MyCompNum,FET,2,Alphas[1],Alphas[2],i,Alphas[1],Alphas[2],0,0,0);
						}
					break;		
				case 4:
					printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R2 with A^%d --> A.",Alphas[3],Betas[3],Alphas[3]);
					Stow_ET_Data(MyCompNum,FET,0,Alphas[3],Betas[3],Alphas[3],0,0,0,0,0);
					break;
				case 6:
					if((Betas[2] > 1) && Betas[3] > 1)
						{
						printf("K4: M = SFD(%d,%d) U SFD(%d,%d) U 2BL H[R], where R comes from setting A^%d --> A and B^%d --> B ",
						Alphas[2],Betas[2],Alphas[3],Betas[3],Alphas[3],Alphas[2]);
						printf("\nin the unique separating curve C in Bdry(H) disjoint from A^%d, B^%d, R1, and R2.",Alphas[3],Alphas[2]);
						Stow_ET_Data(MyCompNum,FET,1,Alphas[2],Betas[2],Alphas[3],Betas[3],Alphas[3],Alphas[2],Alphas[3],Alphas[2]);
						}
					if((Betas[2] == 1) && Betas[3] > 1)
						{
						printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R2 with A^%d --> A.",Alphas[3],Betas[3],Alphas[3]);
						Stow_ET_Data(MyCompNum,FET,2,Alphas[3],Betas[3],Alphas[3],0,0,0,0,0);
						}
					if((Betas[2] > 1) && Betas[3] == 1)
						{
						printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R1 with B^%d --> B.",Alphas[2],Betas[2],Alphas[2]);
						Stow_ET_Data(MyCompNum,FET,3,Alphas[2],Betas[2],Alphas[2],0,0,0,0,0);
						}
					break;
				case 8:
					printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R2 with B^%d --> B.",Alphas[4],Betas[4],Alphas[4]);
					Stow_ET_Data(MyCompNum,FET,0,Alphas[4],Betas[4],Alphas[4],0,0,0,0,0);
					break;
				case 9:
					if((Betas[1] > 1) && Betas[4] > 1)
						{
						printf("K4: M = SFD(%d,%d) U SFD(%d,%d) U 2BL H[R], where R comes from setting A^%d --> A and B^%d --> B",
						Alphas[1],Betas[1],Alphas[4],Betas[4],Alphas[1],Alphas[4]);
						printf("\nin the unique separating curve C in Bdry(H) disjoint from A^%d, B^%d, R1, and R2.",Alphas[1],Alphas[4]);
						Stow_ET_Data(MyCompNum,FET,1,Alphas[1],Betas[1],Alphas[4],Betas[4],Alphas[1],Alphas[4],Alphas[1],Alphas[4]);
						}
					if((Betas[1] == 1) && Betas[4] > 1)
						{
						printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R2 with B^%d --> B.",Alphas[4],Betas[4],Alphas[4]);
						Stow_ET_Data(MyCompNum,FET,2,Alphas[4],Betas[4],Alphas[4],0,0,0,0,0);
						}
					if((Betas[1] > 1) && Betas[4] == 1)
						{
						printf("K1: M = SFD(%d,%d) U 1BKinLS H[R], where R is R1 with A^%d --> A.",Alphas[1],Betas[1],Alphas[1]);
						Stow_ET_Data(MyCompNum,FET,3,Alphas[1],Betas[1],Alphas[1],0,0,0,0,0);
						}
					break;
				case 12:
					i = Betas[3];
					if(Betas[4] > 1) i = Betas[4];
					if(i == 1)
						{
						printf("K3: M = SFD(%d,%d) U 2BK H[R], where R is R2 with A^%d --> A and B^%d --> B.",
						Alphas[3],Alphas[4],Alphas[3],Alphas[4]);
						Stow_ET_Data(MyCompNum,FET,1,Alphas[3],Alphas[4],Alphas[3],Alphas[4],0,0,0,0);
						}
					if(i > 1)
						{
						printf("K3: M = SFD(%d,%d,%d) U 2BK H[R], where R is R2 with A^%d --> A and B^%d --> B.",
						Alphas[3],Alphas[4],i,Alphas[3],Alphas[4]);
						Stow_ET_Data(MyCompNum,FET,2,Alphas[3],Alphas[4],i,Alphas[3],Alphas[4],0,0,0);
						}
					break;
				case 16:
				case 17:
				case 20:
				case 21:
					if(j == 1)
						{
						printf("K5: M = T X I U 2BL(%d,%d).",KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,KorLP1,KorLP2,0,0,0,0,0,0);
						}
					else
						{
						printf("K5: M = SFA(%d) U 2BL(%d,%d).",j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,j,KorLP1,KorLP2,0,0,0,0,0);
						}				
					break;
				case 18:
				case 19:
				case 22:
				case 23:
					if(j == 1)
						{
						printf("K2: M = m X S1 U 2BK(%d,%d).",KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,KorLP1,KorLP2,0,0,0,0,0,0);
						}
					else
						{
						printf("K2: M = SFm(%d) U 2BK(%d,%d).",j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,j,KorLP1,KorLP2,0,0,0,0,0);
						}				
					break;
				case 24:
					if(j == 1)
						{
						printf("K5: M = SFA(%d) U 2BL(%d,%d).",Alphas[1],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[1],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K5: M = SFA(%d,%d) U 2BL(%d,%d).",Alphas[1],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[1],j,KorLP1,KorLP2,0,0,0,0);
						}			
					break;
				case 25:
					if(j == 1)
						{
						printf("K2: M = SFm(%d) U 2BK(%d,%d).",Alphas[1],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[1],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K2: M = SFm(%d,%d) U 2BK(%d,%d).",Alphas[1],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[1],j,KorLP1,KorLP2,0,0,0,0);
						}			
					break;	
				case 26:
					if(j == 1)
						{
						printf("K5: M = SFA(%d) U 2BL(%d,%d).",Alphas[2],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[2],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K5: M = SFA(%d,%d) U 2BL(%d,%d).",Alphas[2],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[2],j,KorLP1,KorLP2,0,0,0,0);
						}			
					break;
				case 27:
					if(j == 1)
						{
						printf("K2: M = SFm(%d) U 2BK(%d,%d).",Alphas[2],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[2],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K2: M = SFm(%d,%d) U 2BK(%d,%d).",Alphas[2],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[2],j,KorLP1,KorLP2,0,0,0,0);
						}				
					break;
				case 28:
					if(j == 1)
						{
						printf("K5: M = SFA(%d) U 2BL(%d,%d).",Alphas[3],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[3],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K5: M = SFA(%d,%d) U 2BL(%d,%d).",Alphas[3],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[3],j,KorLP1,KorLP2,0,0,0,0);
						}			
					break;
				case 29:
					if(j == 1)
						{
						printf("K2: M = SFm(%d) U 2BK(%d,%d).",Alphas[3],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[3],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K2: M = SFm(%d,%d) U 2BK(%d,%d).",Alphas[3],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[3],j,KorLP1,KorLP2,0,0,0,0);
						}			
					break;
				case 30:
					if(j == 1)
						{
						printf("K5: M = SFA(%d) U 2BL(%d,%d).",Alphas[4],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[4],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K5: M = SFA(%d,%d) U 2BL(%d,%d).",Alphas[4],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[4],j,KorLP1,KorLP2,0,0,0,0);
						}				
					break;
				case 31:
					if(j == 1)
						{
						printf("K2: M = SFm(%d) U 2BK(%d,%d).",Alphas[4],KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[4],KorLP1,KorLP2,0,0,0,0,0);
						}
					else
						{
						printf("K2: M = SFm(%d,%d) U 2BK(%d,%d).",Alphas[4],j,KorLP1,KorLP2);
						Stow_ET_Data(MyCompNum,FET,j,Alphas[4],j,KorLP1,KorLP2,0,0,0,0);
						}
					break;																												
				}
			if(F1 || Batch == 10 || Batch == 11)
				{
				printf("\nR1 = %s",(char *) *Relators[1]);
				printf("\nR2 = %s",(char *) *Relators[2]);
				}					
			return(2);				
			}		
		return(1);	
		}
	return(0);									
}

int Get_Genus_2_EXPS(void)
{
    /******************************************************************************************
        For j = 1 and j = 2, this routine does two things. First, it determines the exponents 
    with which each generator appears in Relators[j]. It leaves these exponents in the columns
    of the array EXPAj_SF[] and EXPBj_SF[].
        Second, the routine counts the number of appearances of each exponent and leaves
    these counts in the arrays NEXAj_SF[] and NEXBj_SF[]. (Note exponents are signed here, so 
    e and -e are different exponents.)
    ******************************************************************************************/    
    						
	unsigned char  	i,
					j,
					*p,
					x,
					y;
						
	int   			ex,
					sex,
					*q,
					*r;

	for(j = 1; j <= NumRelators; j++)
		{     
		if(j == 1) for(i = 0; i < 8; i++) NEXA1_SF[i] = NEXB1_SF[i] = EXPA1_SF[i] = EXPB1_SF[i] = 0;                          
		if(j == 2) for(i = 0; i < 8; i++) NEXA2_SF[i] = NEXB2_SF[i] = EXPA2_SF[i] = EXPB2_SF[i] = 0;
	
		p = *Relators[j];
		x = *p++;
		if(!x) return(2);			/* Relators[j] is empty!  */
		ex = 1;
		while(*p == x)
			{
			ex++;
			p++;
			}
		sex = ex;
		ex = 0;
		if(*p) x = *p;
		while( (y = *p++) )
			{
			if(x == y)
				ex++;
			else
				{
				if(j == 1)
					{
					if(x == 'A' || x == 'a') 
						{
						q = EXPA1_SF;
						r = NEXA1_SF;
						}
					else
						{
						q = EXPB1_SF;
						r = NEXB1_SF;
						}
					}				
				if(j == 2)
					{
					if(x == 'A' || x == 'a') 
						{
						q = EXPA2_SF;
						r = NEXA2_SF;
						}
					else
						{
						q = EXPB2_SF;
						r = NEXB2_SF;
						}
					}
				if(x > 96) ex = -ex;		
				for(x = 0; x < 8 && ex != q[x] && q[x]; x++) ;
				if(x == 8) return(4);							/* Too Many Exponents! */
				q[x] = ex;
				r[x]++;
				ex = 1;    
				}
			x = y;
			}
		y = **Relators[j];        
		if(x == y)
			{
			if(j == 1)
				{
				if(x == 'A' || x == 'a') 
					{
					q = EXPA1_SF;
					r = NEXA1_SF;
					}
				else
					{
					q = EXPB1_SF;
					r = NEXB1_SF;
					}
				}							
			if(j == 2)
				{
				if(x == 'A' || x == 'a') 
					{
					q = EXPA2_SF;
					r = NEXA2_SF;
					}
				else
					{
					q = EXPB2_SF;
					r = NEXB2_SF;
					}
				}
			ex += sex;	
			if(x > 96) ex = -ex;		
			for(x = 0; x < 8 && ex != q[x] && q[x]; x++) ;
			if(x == 8) return(5);							/* Too Many Exponents! */
			q[x] = ex;
			r[x]++;
			}
		else
			{
			if(j == 1)
				{
				if(x == 'A' || x == 'a') 
					{
					q = EXPA1_SF;
					r = NEXA1_SF;
					}
				else
					{
					q = EXPB1_SF;
					r = NEXB1_SF;
					}
				}	
			if(j == 2)
				{							
				if(x == 'A' || x == 'a') 
					{
					q = EXPA2_SF;
					r = NEXA2_SF;
					}
				else
					{
					q = EXPB2_SF;
					r = NEXB2_SF;
					}
				}
			if(x > 96) ex = -ex;		
			for(x = 0; x < 8 && ex != q[x] && q[x]; x++) ;
			if(x == 8) return(6);							/* Too Many Exponents! */
			q[x] = ex;
			r[x]++;
		
			ex = sex;
			x = y;
			if(j == 1)
				{
				if(x == 'A' || x == 'a') 
					{
					q = EXPA1_SF;
					r = NEXA1_SF;
					}
				else
					{
					q = EXPB1_SF;
					r = NEXB1_SF;
					}
				}						
			if(j == 2)
				{
				if(x == 'A' || x == 'a') 
					{
					q = EXPA2_SF;
					r = NEXA2_SF;
					}
				else
					{
					q = EXPB2_SF;
					r = NEXB2_SF;
					}
				}
			if(x > 96) ex = -ex;		
			for(x = 0; x < 8 && ex != q[x] && q[x]; x++) ;
			if(x == 8) return(7);							/* Too Many Exponents! */
			q[x] = ex;
			r[x]++;
			}
		}
return(0);            
}

int Genus_Two_Essential_Torus_Betas(char F2)
{
	char		FA,
				FB;

	int			Alp3A,
				Alp3B,
				i,
				j,
				MA,
				MB,
				NA,
				NB;
		
	if(F2 == 1)
		{		
		/*** Check if an 'A' exponent has absolute value > 2 in R1 or R2. ***/
			
		if(Alphas[1] > 2)
			FA = TRUE;
		else for(i = 0, FA  = FALSE; i < 6; i++)
			{
			if(abs(EXPA2_SF[i]) > 2)
				{
				FA = TRUE;
				break;
				}
			}
			
		if(FA)
			{
			for(i = MA = 0; i < 6; i++)
				{
				j = abs(EXPA2_SF[i]);
				if(j && j != Alphas[1] && j > MA) MA = j;
				}
			if(MA == 0)
				{
				Betas[1] = 0;
				return(0);					
				}	
			for(i = NA = 0; i < 6; i++)
				{
				j = abs(EXPA2_SF[i]);
				if(j && j != Alphas[1] && j != MA)
					{
					NA = j;
					break;
					}
				}
			if(NA == 0)
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA2_SF[i];
					if(j ==  MA) Alp3A += NEXA2_SF[i];
					if(j == -MA) Alp3A -= NEXA2_SF[i];
					}		
				}
			if(NA && (MA < Alphas[1]))
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA2_SF[i];
					if(j ==  MA) Alp3A += NEXA2_SF[i];
					if(j == -MA) Alp3A -= NEXA2_SF[i];
					if(j ==  NA) Alp3A -= NEXA2_SF[i];
					if(j == -NA) Alp3A += NEXA2_SF[i];
					}							
				}
			if(NA && (MA > Alphas[1]))
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA2_SF[i];
					if(j ==  MA) Alp3A += NEXA2_SF[i];
					if(j == -MA) Alp3A -= NEXA2_SF[i];
					if(j ==  NA) Alp3A += NEXA2_SF[i];
					if(j == -NA) Alp3A -= NEXA2_SF[i];
					}							
				}
			Betas[1] = abs(Alp3A);
			return(1);					
			}
		j = Get_Betas2(2,'A');		
		Betas[1] = abs(j);	
		if(Betas[1]) return(1);	
		return(0);	
		}
		
	if(F2 == 2)
		{			
		/*** Check if a 'B' exponent has absolute value > 2 in R1 or R2. ***/
		
		if(Alphas[2] > 2)
			FB = TRUE;
		else for(i = 0, FB  = FALSE; i < 6; i++)
			{
			if(abs(EXPB2_SF[i]) > 2)
				{
				FB = TRUE;
				break;
				}
			}
			
		if(FB)
			{
			for(i = MB = 0; i < 6; i++)
				{
				j = abs(EXPB2_SF[i]);
				if(j && j != Alphas[2] && j > MB) MB = j;
				}
			if(MB == 0)
				{
				Betas[2] = 0;
				return(0);					
				}	
			for(i = NB = 0; i < 6; i++)
				{
				j = abs(EXPB2_SF[i]);
				if(j && j != Alphas[2] && j != MB)
					{
					NB = j;
					break;
					}
				}
			if(NB == 0)
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB2_SF[i];
					if(j ==  MB) Alp3B += NEXB2_SF[i];
					if(j == -MB) Alp3B -= NEXB2_SF[i];
					}		
				}
			if(NB && (MB < Alphas[2]))
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB2_SF[i];
					if(j ==  MB) Alp3B += NEXB2_SF[i];
					if(j == -MB) Alp3B -= NEXB2_SF[i];
					if(j ==  NB) Alp3B -= NEXB2_SF[i];
					if(j == -NB) Alp3B += NEXB2_SF[i];
					}							
				}
			if(NB && (MB > Alphas[2]))
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB2_SF[i];
					if(j ==  MB) Alp3B += NEXB2_SF[i];
					if(j == -MB) Alp3B -= NEXB2_SF[i];
					if(j ==  NB) Alp3B += NEXB2_SF[i];
					if(j == -NB) Alp3B -= NEXB2_SF[i];
					}							
				}
			Betas[2] = abs(Alp3B);
			return(1);
			}
		j = Get_Betas2(2,'B');		
		Betas[2] = abs(j);	
		if(Betas[2]) return(1);	
		return(0);	
		}
		
	if(F2 == 3)
		{		
		/*** Check if an 'A' exponent has absolute value > 2 in R1 or R2. ***/
			
		if(Alphas[3] > 2)
			FA = TRUE;
		else for(i = 0, FA  = FALSE; i < 6; i++)
			{
			if(abs(EXPA1_SF[i]) > 2)
				{
				FA = TRUE;
				break;
				}
			}
			
		if(FA)
			{
			for(i = MA = 0; i < 6; i++)
				{
				j = abs(EXPA1_SF[i]);
				if(j && j != Alphas[3] && j > MA) MA = j;
				}
			if(MA == 0)
				{
				Betas[3] = 0;
				return(0);					
				}	
			for(i = NA = 0; i < 6; i++)
				{
				j = abs(EXPA1_SF[i]);
				if(j && j != Alphas[3] && j != MA)
					{
					NA = j;
					break;
					}
				}
			if(NA == 0)
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA1_SF[i];
					if(j ==  MA) Alp3A += NEXA1_SF[i];
					if(j == -MA) Alp3A -= NEXA1_SF[i];
					}		
				}
			if(NA && (MA < Alphas[3]))
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA1_SF[i];
					if(j ==  MA) Alp3A += NEXA1_SF[i];
					if(j == -MA) Alp3A -= NEXA1_SF[i];
					if(j ==  NA) Alp3A -= NEXA1_SF[i];
					if(j == -NA) Alp3A += NEXA1_SF[i];
					}							
				}
			if(NA && (MA > Alphas[3]))
				{
				for(i = Alp3A = 0; i < 6; i++)
					{
					j = EXPA1_SF[i];
					if(j ==  MA) Alp3A += NEXA1_SF[i];
					if(j == -MA) Alp3A -= NEXA1_SF[i];
					if(j ==  NA) Alp3A += NEXA1_SF[i];
					if(j == -NA) Alp3A -= NEXA1_SF[i];
					}							
				}
			Betas[3] = abs(Alp3A);
			return(1);					
			}
		j = Get_Betas2(1,'A');		
		Betas[3] = abs(j);	
		if(Betas[3]) return(1);			
		return(0);		
		}

	if(F2 == 4)
		{			
		/*** Check if a 'B' exponent has absolute value > 2 in R1 or R2. ***/
		
		if(Alphas[4] > 2)
			FB = TRUE;
		else for(i = 0, FB  = FALSE; i < 6; i++)
			{
			if(abs(EXPB1_SF[i]) > 2)
				{
				FB = TRUE;
				break;
				}
			}
			
		if(FB)
			{
			for(i = MB = 0; i < 6; i++)
				{
				j = abs(EXPB1_SF[i]);
				if(j && j != Alphas[4] && j > MB) MB = j;
				}
			if(MB == 0)
				{
				Betas[4] = 0;
				return(0);					
				}	
			for(i = NB = 0; i < 6; i++)
				{
				j = abs(EXPB1_SF[i]);
				if(j && j != Alphas[4] && j != MB)
					{
					NB = j;
					break;
					}
				}
			if(NB == 0)
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB1_SF[i];
					if(j ==  MB) Alp3B += NEXB1_SF[i];
					if(j == -MB) Alp3B -= NEXB1_SF[i];
					}		
				}
			if(NB && (MB < Alphas[4]))
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB1_SF[i];
					if(j ==  MB) Alp3B += NEXB1_SF[i];
					if(j == -MB) Alp3B -= NEXB1_SF[i];
					if(j ==  NB) Alp3B -= NEXB1_SF[i];
					if(j == -NB) Alp3B += NEXB1_SF[i];
					}							
				}
			if(NB && (MB > Alphas[4]))
				{
				for(i = Alp3B = 0; i < 6; i++)
					{
					j = EXPB1_SF[i];
					if(j ==  MB) Alp3B += NEXB1_SF[i];
					if(j == -MB) Alp3B -= NEXB1_SF[i];
					if(j ==  NB) Alp3B += NEXB1_SF[i];
					if(j == -NB) Alp3B -= NEXB1_SF[i];
					}							
				}
			Betas[4] = abs(Alp3B);
			return(1);
			}
		j = Get_Betas2(1,'B');		
		Betas[4] = abs(j);	
		if(Betas[4]) return(1);			
		return(0);	
		}
	return(0);					
}

int Get_Betas2(char WhichRelator,char WhichSquare)
{
	unsigned char	*p,
					*q,
					x,
					y,
					z;
			
	int				Beta = 0,
					i,
					mexp;
	
	if(WhichRelator == 1) 
		{
		if(GetHandleSize((char**) Relators[1]) < 4) return(0);
		q = *Relators[1];
		}
	if(WhichRelator == 2) 
		{
		if(GetHandleSize((char**) Relators[2]) < 4) return(0);
		q = *Relators[2];
		}
	
	/* Compute Beta with: Beta = |ABA| + |Aba| + |abA| + |AbA| -|aba| - |ABa| - |aBA| - |aBa| */
	
	if(WhichSquare == 'B')
		{
		mexp = 0;
		for(i = 0; i < 6; i++) if(abs(EXPA1_SF[i]) > mexp) mexp = abs(EXPA1_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPA2_SF[i]) > mexp) mexp = abs(EXPA2_SF[i]);
		if(mexp < 2) return(0);
		p = q;
		x = *p++;
		y = *p++;
		z = *p++;
		while(1)
			{
			if(y == 'B')
				{
				if(x == 'A')
					{
					if(z == 'A') Beta ++; /* ABA */
					if(z == 'a') Beta --; /* ABa */
					}
				if(x == 'a')
					{
					if(z == 'A') Beta --; /* aBA */
					if(z == 'a') Beta --; /* aBa */					
					}	
				}
			if(y == 'b')
				{
				if(x == 'A')
					{
					if(z == 'A') Beta ++; /* AbA */
					if(z == 'a') Beta ++; /* Aba */
					}
				if(x == 'a')
					{
					if(z == 'A') Beta ++; /* abA */
					if(z == 'a') Beta --; /* aba */					
					}					
				}
			x = y;
			y = z;
			z = *p++;
			if(z == EOS) 
				{
				p = q;
				z = *p++;
				}
			if((p - q) == 3) break;		
			}
		}
		
	if(WhichSquare == 'A')	
		{
		mexp = 0;
		for(i = 0; i < 6; i++) if(abs(EXPB1_SF[i]) > mexp) mexp = abs(EXPB1_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB2_SF[i]) > mexp) mexp = abs(EXPB2_SF[i]);
		if(mexp < 2) return(0);		
		p = q;
		x = *p++;
		y = *p++;
		z = *p++;
		while(1)
			{
			if(y == 'A')
				{
				if(x == 'B')
					{
					if(z == 'B') Beta ++; /* BAB */
					if(z == 'b') Beta --; /* BAb */
					}
				if(x == 'b')
					{
					if(z == 'B') Beta --; /* bAB */
					if(z == 'b') Beta --; /* bAb */					
					}	
				}
			if(y == 'a')
				{
				if(x == 'B')
					{
					if(z == 'B') Beta ++; /* BaB */
					if(z == 'b') Beta ++; /* Bab */
					}
				if(x == 'b')
					{
					if(z == 'B') Beta ++; /* baB */
					if(z == 'b') Beta --; /* bab */					
					}					
				}
			x = y;
			y = z;
			z = *p++;
			if(z == EOS) 
				{
				p = q;
				z = *p++;
				}
			if((p - q) == 3) break;		
			}
		}
	return(Beta);		
}

int Stow_ET_Data(int MyCompNum,char FET,int P0,int P1,int P2,int P3,int P4,int P5,int P6,int P7,int P8)
{
	unsigned char	*p,
					*q;

	if(Batch < 10 || Batch > 11) return(0);
	if(H_Results == NULL) return(0);
	
	if(SFSols[MyCompNum]) DisposePtr((int*) SFSols[MyCompNum]);
	SFSols[MyCompNum] = (int*) NewPtr(sizeof(int)*10);
	if(SFSols[MyCompNum] == NULL) Mem_Error();
	SFSols[MyCompNum][0] = FET;
	SFSols[MyCompNum][1] = P0;
	SFSols[MyCompNum][2] = P1;
	SFSols[MyCompNum][3] = P2;
	SFSols[MyCompNum][4] = P3;
	SFSols[MyCompNum][5] = P4;
	SFSols[MyCompNum][6] = P5;
	SFSols[MyCompNum][7] = P6;
	SFSols[MyCompNum][8] = P7;
	SFSols[MyCompNum][9] = P8;
	
	if(SETR1[MyCompNum] != NULL) DisposePtr((char **) SETR1[MyCompNum]);
	SETR1[MyCompNum] = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[1]));
	if(SETR1[MyCompNum] == NULL) Mem_Error();
	q = SETR1[MyCompNum];
	p = *Relators[1];
	while( (*q++ = *p++) ) ;
	
	if(NumRelators > 1)
		{
		if(SETR2[MyCompNum] != NULL) DisposePtr((char **) SETR2[MyCompNum]);
		SETR2[MyCompNum] = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[2]));
		if(SETR2[MyCompNum] == NULL) Mem_Error();
		q = SETR2[MyCompNum];
		p = *Relators[2];
		while( (*q++ = *p++) ) ;
		if(NumRelators > 2)
			{
			if(SETR3[MyCompNum] != NULL) DisposePtr((char **) SETR3[MyCompNum]);
			SETR3[MyCompNum] = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[3]));
			if(SETR3[MyCompNum] == NULL) Mem_Error();
			q = SETR3[MyCompNum];
			p = *Relators[3];
			while( (*q++ = *p++) ) ;
			}
		}
	if(NumRelators < 3)
		{
		if(SETR3[MyCompNum] != NULL) DisposePtr((char **) SETR3[MyCompNum]);
		SETR3[MyCompNum] = NULL;
		}
	if(NumRelators < 2)
		{
		if(SETR2[MyCompNum] != NULL) DisposePtr((char **) SETR2[MyCompNum]);
		SETR2[MyCompNum] = NULL;
		}			
	
	return(0);
}

int Print_ET_Data(int MyCompNum)
{
	int FET,
		P0,
		P1,
		P2,
		P3,
		P4,
		P5,
		P6,
		P7,
		P8;
	
	if(H_Results == NULL) return(0);
	
	P0 = SFSols[MyCompNum][1];
	P1 = SFSols[MyCompNum][2];
	P2 = SFSols[MyCompNum][3];
	P3 = SFSols[MyCompNum][4];
	P4 = SFSols[MyCompNum][5];
	P5 = SFSols[MyCompNum][6];
	P6 = SFSols[MyCompNum][7];
	P7 = SFSols[MyCompNum][8];
	P8 = SFSols[MyCompNum][9];		
	
	FET = SFSols[MyCompNum][0];

	switch(FET)
		{
		case 1:
			fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R1 with A^%d --> A.",P1,P2,P3);
			break;
		case 2:
			fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R1 with B^%d --> B.",P1,P2,P3);
			break;
		case 3:
			if(P0 == 1)
				fprintf(H_Results," K3: SFD(%d,%d) U 2BK H[R], where R is R1 with A^%d --> A and B^%d --> B.",P1,P2,P3,P4);
			if(P0 == 2)
				fprintf(H_Results," K3: SFD(%d,%d,%d) U 2BK H[R], where R is R1 with A^%d --> A and B^%d --> B.",P1,P2,P3,P4,P5);
			break;		
		case 4:
			fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R2 with A^%d --> A.",P1,P2,P3);
			break;
		case 6:
			if(P0 == 1)
				{
				fprintf(H_Results," K4: SFD(%d,%d) U SFD(%d,%d) U 2BL H[R], where R comes from setting A^%d --> A and B^%d --> B ",
				P1,P2,P3,P4,P5,P6);
				fprintf(H_Results,"in the unique separating curve C in Bdry(H) disjoint from A^%d, B^%d, R1, and R2.",P7,P8);
				}
			if(P0 == 2)
				fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R2 with A^%d --> A.",P1,P2,P3);
			if(P0 == 3)
				fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R1 with B^%d --> B.",P1,P2,P3);
			break;
		case 8:
			fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R2 with B^%d --> B.",P1,P2,P3);
			break;
		case 9:
			if(P0 == 1)
				{
				fprintf(H_Results," K4: SFD(%d,%d) U SFD(%d,%d) U 2BL H[R], where R comes from setting A^%d --> A and B^%d --> B ",
				P1,P2,P3,P4,P5,P6);
				fprintf(H_Results,"in the unique separating curve C in Bdry(H) disjoint from A^%d, B^%d, R1, and R2.",P7,P8);
				}
			if(P0 == 2)
				fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R2 with B^%d --> B.",P1,P2,P3);
			if(P0 == 3)
				fprintf(H_Results," K1: SFD(%d,%d) U 1BKinLS H[R], where R is R1 with A^%d --> A.",P1,P2,P3);
			break;
		case 12:
			if(P0 == 1)
				fprintf(H_Results," K3: SFD(%d,%d) U 2BK H[R], where R is R2 with A^%d --> A and B^%d --> B.",P1,P2,P3,P4);
			if(P0 == 2)
				fprintf(H_Results," K3: SFD(%d,%d,%d) U 2BK H[R], where R is R2 with A^%d --> A and B^%d --> B.",P1,P2,P3,P4,P5);
			break;
		case 16:
		case 17:
		case 20:
		case 21:
			if(P0 == 1) fprintf(H_Results," K5: T X I U 2BL(%d,%d).",P1,P2);
			else		fprintf(H_Results," K5: SFA(%d) U 2BL(%d,%d).",P1,P2,P3);
			break;
		case 18:
		case 19:
		case 22:
		case 23:
			if(P0 == 1) fprintf(H_Results," K2: M X S1 U 2BK(%d,%d).",P1,P2);
			else		fprintf(H_Results," K2: SFM(%d) U 2BK(%d,%d).",P1,P2,P3);
			break;
		case 24:
			if(P0 == 1) fprintf(H_Results," K5: SFA(%d) U 2BL(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K5: SFA(%d,%d) U 2BL(%d,%d).",P1,P2,P3,P4);
			break;		
		case 25:
			if(P0 == 1) fprintf(H_Results," K2: SFM(%d) U 2BK(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K2: SFM(%d,%d) U 2BK(%d,%d).",P1,P2,P3,P4);
			break;	
		case 26:
			if(P0 == 1) fprintf(H_Results," K5: SFA(%d) U 2BL(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K5: SFA(%d,%d) U 2BL(%d,%d).",P1,P2,P3,P4);
			break;		
		case 27:			
			if(P0 == 1) fprintf(H_Results," K2: SFM(%d) U 2BK(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K2: SFM(%d,%d) U 2BK(%d,%d).",P1,P2,P3,P4);
			break;
		case 28:
			if(P0 == 1) fprintf(H_Results," K5: SFA(%d) U 2BL(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K5: SFA(%d,%d) U 2BL(%d,%d).",P1,P2,P3,P4);
			break;
		case 29:
			if(P0 == 1) fprintf(H_Results," K2: SFM(%d) U 2BK(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K2: SFM(%d,%d) U 2BK(%d,%d).",P1,P2,P3,P4);
			break;		
		case 30:
			if(P0 == 1) fprintf(H_Results," K5: SFA(%d) U 2BL(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K5: SFA(%d,%d) U 2BL(%d,%d).",P1,P2,P3,P4);
			break;		
		case 31:
			if(P0 == 1) fprintf(H_Results," K2: SFM(%d) U 2BK(%d,%d).",P1,P2,P3);
			else		fprintf(H_Results," K2: SFM(%d,%d) U 2BK(%d,%d).",P1,P2,P3,P4);
			break;
		case 50:
			fprintf(H_Results," ET: R%d is disjoint from cutting disk D_%c of the underlying handlebody H.",P1,P2);
			fprintf(H_Results,"\nIf h = H - D_%c and h' = H' - D_R%d, then T = Bdry h[R%d] = Bdry h'[Bdry D_%c] is an essential torus."
			,P2,P1,P1,P2);				
		}
		
	fprintf(H_Results,"\nR1 = %s",SETR1[MyCompNum]);
	if(SETR2[MyCompNum] != NULL) fprintf(H_Results,"\nR2 = %s",SETR2[MyCompNum]);
	if(SETR3[MyCompNum] != NULL) fprintf(H_Results,"\nR3 = %s",SETR3[MyCompNum]);
	if(SETR4[MyCompNum] != NULL)
		{
		fprintf(H_Results,"\nBdry D_%c = %s",P2,SETR4[MyCompNum]);
		DisposePtr((char **) SETR4[MyCompNum]);
		SETR4[MyCompNum] = NULL;
		}
		
	return(0);	
}

int	CheckForAltExpSigns(char WhichRelator, char WhichGen)
{
	unsigned char	*p,
					*q,
					sex,
					x,
					y;
					
	/***************************************************************************************************
		This routine checks whether the exponents of WhichGen, known to all be ±1, alternate in sign in 
		WhichRelator. It returns 1 if the exponents of WhichGen are alternately ±1 and otherwise returns
		zero.	
	****************************************************************************************************/				
	
	if(WhichRelator == 1) 
		{
		if(GetHandleSize((char**) Relators[1]) < 5) return(0);
		q = *Relators[1];
		}
	if(WhichRelator == 2) 
		{
		if(GetHandleSize((char**) Relators[2]) < 5) return(0);
		q = *Relators[2];
		}
		
	if(WhichGen == 'A')
		{
		for(p = q; (x = *p); p++) if((x == 'A' || x == 'a'))
			{
			y = x;
			sex = x;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'A' || x == 'a')) 
			{
			if(x == y) return(0);
			y = x;
			}
		if(x == EOS && y == sex) return(0);
		return(1);
		}
		
	if(WhichGen == 'B')
		{
		for(p = q; (x = *p); p++) if((x == 'B' || x == 'b'))
			{
			y = x;
			sex = x;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'B' || x == 'b')) 
			{
			if(x == y) return(0);
			y = x;
			}
		if((x == EOS && y == sex)) return(0);
		return(1);
		}
	return(0);	
}

int Get2BKorLPs(char WhichRelator,char WhichGen,unsigned int* Ptr1,unsigned int* Ptr2)
{
	unsigned char	*p,
					*q,
					x,
					y,
					z;
					
	unsigned int 	P1 = 0,
					P2 = 0;				
	
	if(WhichRelator == 1) 
		{
		if(GetHandleSize((char**) Relators[1]) < 5) return(0);
		q = *Relators[1];
		}
	if(WhichRelator == 2) 
		{
		if(GetHandleSize((char**) Relators[2]) < 5) return(0);
		q = *Relators[2];
		}
	
	/* If WhichGen == 'A', P1 = |BAB| + |bab| and P2 = |BAb| + |Bab|. */
	
	if(WhichGen == 'A')
		{
		p = q;
		x = *p++;
		y = *p++;
		z = *p++;
		while(1)
			{
			if(y == 'A' && x == 'B')
				{
				if(z == 'B') P1 ++; /* BAB */
				if(z == 'b') P2 ++; /* BAb */
				}	
			if(y == 'a' && z == 'b')
				{
				if(x == 'B') P2 ++; /* Bab */
				if(x == 'b') P1 ++; /* bab */					
				}
			x = y;
			y = z;
			z = *p++;
			if(z == EOS) 
				{
				p = q;
				z = *p++;
				}
			if((p - q) == 3) break;		
			}
		}
			
	/* If WhichGen == 'B', P1 = |ABA| + |aba| and P2 = |ABa| + |Aba|. */
	
	if(WhichGen == 'B')
		{
		p = q;
		x = *p++;
		y = *p++;
		z = *p++;
		while(1)
			{
			if(y == 'B' && x == 'A')
				{
				if(z == 'A') P1 ++; /* ABA */
				if(z == 'a') P2 ++; /* ABa */
				}	
			if(y == 'b' && z == 'a')
				{
				if(x == 'A') P2 ++; /* Aba */
				if(x == 'a') P1 ++; /* aba */					
				}
			x = y;
			y = z;
			z = *p++;
			if(z == EOS) 
				{
				p = q;
				z = *p++;
				}
			if((p - q) == 3) break;		
			}
		}
	
	*Ptr1 = P1;
	*Ptr2 = P2;
		
	return(0);		
}

int GetAlpha2(char WhichRelator,char WhichGen)
{
	int				Alpha2 = 0,
					i;
			
	unsigned int 	MAExp = 0,
					MBExp = 0;
	
	/* 	This routine computes Alpha2 by counting the net number of appearances of X^2 and x^2
		in Relator 'WhichRelator' when X is 'WhichGen' and both 'A' and 'B' appear in R1 union 
		R2 with exponents of absolute value greater than one. */

	for(i = 0; i < 6; i++)
		{
		if(abs(EXPA1_SF[i]) > MAExp) MAExp = abs(EXPA1_SF[i]);
		if(abs(EXPA2_SF[i]) > MAExp) MAExp = abs(EXPA2_SF[i]);
		}
	if(MAExp < 2) return(0);
	for(i = 0; i < 6; i++)
		{
		if(abs(EXPB1_SF[i]) > MBExp) MBExp = abs(EXPB1_SF[i]);
		if(abs(EXPB2_SF[i]) > MBExp) MBExp = abs(EXPB2_SF[i]);
		}
	if(MBExp < 2) return(0);
	
	if(WhichRelator == 1)
		{			
		if(WhichGen == 'A') for(i = 0; i < 6; i++) 
			{
			if(EXPA1_SF[i] ==  2) Alpha2 += NEXA1_SF[i];
			if(EXPA1_SF[i] == -2) Alpha2 -= NEXA1_SF[i];
			}
		if(WhichGen == 'B') for(i = 0; i < 6; i++)
			{
			if(EXPB1_SF[i] ==  2) Alpha2 += NEXB1_SF[i];
			if(EXPB1_SF[i] == -2) Alpha2 -= NEXB1_SF[i];
			}
		}
		
	if(WhichRelator == 2)	
		{
		if(WhichGen == 'A') for(i = 0; i < 6; i++) 
			{
			if(EXPA2_SF[i] ==  2) Alpha2 += NEXA2_SF[i];
			if(EXPA2_SF[i] == -2) Alpha2 -= NEXA2_SF[i];
			}
		if(WhichGen == 'B') for(i = 0; i < 6; i++)
			{
			if(EXPB2_SF[i] ==  2) Alpha2 += NEXB2_SF[i];
			if(EXPB2_SF[i] == -2) Alpha2 -= NEXB2_SF[i];
			}
		}
								
	return(abs(Alpha2));
}

int GetAlpha2Sub1(char WhichRelator,char WhichGen)
{
	unsigned char	*p,
					*q,
					x,
					y,
					z,
					w;
					
	int				Alpha2 = 0,
					i,
					NABBA = 0,
					Nabba = 0,
					NAbbA = 0,
					NaBBa = 0,
					NBAAB = 0,
					Nbaab = 0,
					NBaaB = 0,
					NbAAb = 0;
			
	unsigned int 	MAExp = 0,
					MBExp = 0;
	
	/* 	This routine computes Alpha2 by counting the net number of appearances of X^2 and x^2 in
		Relator 'WhichRelator' when X is 'WhichGen', X^2 or x^2 appears in Relator 'WhichRelator',
		and the other generator appears in Relator 'WhichRelator' only with exponents ±1. */
	
	if(WhichRelator == 1)
		{
		if(GetHandleSize((char**) Relators[1]) < 5) return(0);		
		for(i = 0; i < 6; i++) if(abs(EXPA1_SF[i]) > MAExp) MAExp = abs(EXPA1_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB1_SF[i]) > MBExp) MBExp = abs(EXPB1_SF[i]);
		if(WhichGen == 'A')
			{
			if(MAExp != 2) return(0);
			if(MBExp != 1) return(0);
			}
		if(WhichGen == 'B')
			{
			if(MAExp != 1) return(0);
			if(MBExp != 2) return(0);
			}
		q = *Relators[1];	
		if(WhichGen == 'A')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			w = *p++;
			while(1)
				{
				if(x == 'B' && w == 'B')
					{
					if(y == 'A' && z == 'A') NBAAB ++; /* BAAB */
					if(y == 'a' && z == 'a') NBaaB ++; /* BaaB */
					}	
				if(x == 'b' && w == 'b')
					{
					if(y == 'A' && z == 'A') NbAAb ++; /* bAAb */
					if(y == 'a' && z == 'a') Nbaab ++; /* baab */					
					}
				x = y;
				y = z;
				z = w;
				w = *p++;
				if(w == EOS) 
					{
					p = q;
					w = *p++;
					}
				if((p - q) == 4) break;		
				}
			}		
		if(WhichGen == 'B')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			w = *p++;
			while(1)
				{
				if(x == 'A' && w == 'A')
					{
					if(y == 'B' && z == 'B') NABBA ++; /* ABBA */
					if(y == 'b' && z == 'b') NAbbA ++; /* AbbA */
					}	
				if(x == 'a' && w == 'a')
					{
					if(y == 'B' && z == 'B') NaBBa ++; /* aBBa */
					if(y == 'b' && z == 'b') Nabba ++; /* abba */					
					}
				x = y;
				y = z;
				z = w;
				w = *p++;
				if(w == EOS) 
					{
					p = q;
					w = *p++;
					}
				if((p - q) == 4) break;		
				}
			}		
		}
		
	if(WhichRelator == 2)	
		{
		if(GetHandleSize((char**) Relators[2]) < 5) return(0);			
		for(i = 0; i < 6; i++) if(abs(EXPA2_SF[i]) > MAExp) MAExp = abs(EXPA2_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB2_SF[i]) > MBExp) MBExp = abs(EXPB2_SF[i]);
		if(WhichGen == 'A')
			{
			if(MAExp != 2) return(0);
			if(MBExp != 1) return(0);
			}
		if(WhichGen == 'B')
			{
			if(MAExp != 1) return(0);
			if(MBExp != 2) return(0);
			}
		q = *Relators[2];	
		if(WhichGen == 'A')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			w = *p++;
			while(1)
				{
				if(x == 'B' && w == 'B')
					{
					if(y == 'A' && z == 'A') NBAAB ++; /* BAAB */
					if(y == 'a' && z == 'a') NBaaB ++; /* BaaB */
					}	
				if(x == 'b' && w == 'b')
					{
					if(y == 'A' && z == 'A') NbAAb ++; /* bAAb */
					if(y == 'a' && z == 'a') Nbaab ++; /* baab */					
					}
				x = y;
				y = z;
				z = w;
				w = *p++;
				if(w == EOS) 
					{
					p = q;
					w = *p++;
					}
				if((p - q) == 4) break;		
				}
			}		
		if(WhichGen == 'B')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			w = *p++;
			while(1)
				{
				if(x == 'A' && w == 'A')
					{
					if(y == 'B' && z == 'B') NABBA ++; /* ABBA */
					if(y == 'b' && z == 'b') NAbbA ++; /* AbbA */
					}	
				if(x == 'a' && w == 'a')
					{
					if(y == 'B' && z == 'B') NaBBa ++; /* aBBa */
					if(y == 'b' && z == 'b') Nabba ++; /* abba */					
					}
				x = y;
				y = z;
				z = w;
				w = *p++;
				if(w == EOS) 
					{
					p = q;
					w = *p++;
					}
				if((p - q) == 4) break;		
				}
			}		
		}
	
	if(WhichGen == 'A')
		{
		if((NBAAB + Nbaab) >= (NbAAb + NBaaB)) 
			Alpha2 = abs(NBAAB - Nbaab);
		else 
			Alpha2 = abs(NbAAb - NBaaB);
		}
	if(WhichGen == 'B')
		{
		if((NABBA + Nabba) >= (NaBBa + NAbbA)) 
			Alpha2 = abs(NABBA - Nabba);
		else
			Alpha2 = abs(NaBBa - NAbbA);	
		}							
	return(Alpha2);
}

int GetAlpha2Sub2(char WhichRelator,char WhichGen)
{
	unsigned char	*p,
					*q,
					x,
					y,
					z;
					
	int 			Alpha2,
					i,
					MAExp = 0,
					MBExp = 0,
					NABA = 0,
					Naba = 0,
					NAbA = 0,
					NaBa = 0,
					NBAB = 0,
					Nbab = 0,
					NbAb = 0,
					NBaB = 0;
	
	/* 	This routine computes Alpha2 in those cases in which 'WhichGen' appears in the relator
		'WhichRelator' only with exponent one. If X = 'WhichGen' and Y is the complementary 
		generator, either the pair (XYX)^±1 or (XyX)^±1 occurs in 'WhichRelator'. Then there
		exists an automorphism of the form X --> Xy or X --> XY which leaves the other
		relator fixed, and leaves both X and Y appearing in 'WhichRelator' with exponents
		having absolute value greater than one. Then Alpha2 = abs(|X^2| - |x^2|).			*/
		
	if(WhichRelator == 1)
		{
		if(GetHandleSize((char**) Relators[1]) < 5) return(0);		
		for(i = 0; i < 6; i++) if(abs(EXPA1_SF[i]) > MAExp) MAExp = abs(EXPA1_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB1_SF[i]) > MBExp) MBExp = abs(EXPB1_SF[i]);	
		if(WhichGen == 'A' && MAExp != 1) return(0);
		if(WhichGen == 'B' && MBExp != 1) return(0);
		q = *Relators[1];
		if(WhichGen == 'A')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			while(1)
				{
				if(x == 'A' && z == 'A')
					{
					if(y == 'B') NABA ++; /* ABA */
					if(y == 'b') NAbA ++; /* AbA */
					}	
				if(x == 'a' && z == 'a')
					{
					if(y == 'B') NaBa ++; /* aBa */
					if(y == 'b') Naba ++; /* aba */					
					}
				x = y;
				y = z;
				z = *p++;
				if(z == EOS) 
					{
					p = q;
					z = *p++;
					}
				if((p - q) == 3) break;		
				}
			}
		if(WhichGen == 'B')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			while(1)
				{
				if(x == 'B' && z == 'B')
					{
					if(y == 'A') NBAB ++; /* BAB */
					if(y == 'a') NBaB ++; /* BaB */
					}	
				if(x == 'b' && z == 'b')
					{
					if(y == 'A') NbAb ++; /* bAb */
					if(y == 'a') Nbab ++; /* bab */					
					}
				x = y;
				y = z;
				z = *p++;
				if(z == EOS) 
					{
					p = q;
					z = *p++;
					}
				if((p - q) == 3) break;		
				}
			}			
		}
				
	if(WhichRelator == 2) 
		{
		if(GetHandleSize((char**) Relators[2]) < 5) return(0);
		for(i = 0; i < 6; i++) if(abs(EXPA2_SF[i]) > MAExp) MAExp = abs(EXPA2_SF[i]);
		for(i = 0; i < 6; i++) if(abs(EXPB2_SF[i]) > MBExp) MBExp = abs(EXPB2_SF[i]);	
		if(WhichGen == 'A' && MAExp != 1) return(0);
		if(WhichGen == 'B' && MBExp != 1) return(0);
		q = *Relators[2];
		if(WhichGen == 'A')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			while(1)
				{
				if(x == 'A' && z == 'A')
					{
					if(y == 'B') NABA ++; /* ABA */
					if(y == 'b') NAbA ++; /* AbA */
					}	
				if(x == 'a' && z == 'a')
					{
					if(y == 'B') NaBa ++; /* aBa */
					if(y == 'b') Naba ++; /* aba */					
					}
				x = y;
				y = z;
				z = *p++;
				if(z == EOS) 
					{
					p = q;
					z = *p++;
					}
				if((p - q) == 3) break;		
				}
			}
		if(WhichGen == 'B')
			{
			p = q;
			x = *p++;
			y = *p++;
			z = *p++;
			while(1)
				{
				if(x == 'B' && z == 'B')
					{
					if(y == 'A') NBAB ++; /* BAB */
					if(y == 'a') NBaB ++; /* BaB */
					}	
				if(x == 'b' && z == 'b')
					{
					if(y == 'A') NbAb ++; /* bAb */
					if(y == 'a') Nbab ++; /* bab */					
					}
				x = y;
				y = z;
				z = *p++;
				if(z == EOS) 
					{
					p = q;
					z = *p++;
					}
				if((p - q) == 3) break;		
				}
			}			
		}
		
	if(WhichGen == 'A')
		{
		if((NABA + Naba) >= (NAbA + NaBa))
			Alpha2 = abs(NABA - Naba);
		else
			Alpha2 = abs(NAbA - NaBa);
		}
	if(WhichGen == 'B')
		{
		if((NBAB + Nbab) >= (NBaB + NbAb))
			Alpha2 = abs(NBAB - Nbab);
		else
			Alpha2 = abs(NBaB - NbAb);
		}
				
	return(Alpha2);	
}

int Init_Genus_Three_Essential_Tori(int* MyTable,int MyStart,int MyCompNum,char F1)
{
	unsigned char	*p,
					*q;
					
	int				i,
					n,
					MyNumGens,
					MyNumRels,
					NumPresChecked;

	/***************************************************************************************
	 	Check which genus three presentations of closed manifolds have disjoint disks and 
		hence essential tori. 
	***************************************************************************************/	

	if(Do_Not_Reduce_Genus == TRUE) return(0);

	for(n = MyStart,NumPresChecked = 0,MyNumGens = MyNumRels = 0; n >= 0; n--) 
		{
		ReadPres 		= MyTable[n];
		if(CS[ComponentNum[ReadPres]] == 1) continue;
		if(ComponentNum[ReadPres] >  MyCompNum) continue;
		if(ComponentNum[ReadPres] <  MyCompNum) return(n);
		if(MyNumGens == 0) MyNumGens = NG[ReadPres];
		if(MyNumRels == 0) MyNumRels = NR[ReadPres];
		if(MyNumGens != 3) continue;
		if(MyNumRels != 3) continue;		
		NumGenerators 	= NG[ReadPres];
		NumRelators 	= NR[ReadPres];
		if(NumGenerators != 3) continue;
		if(NumRelators != 3) continue;
		Vertices		= 2*NumGenerators;
		Length 			= SURL[ReadPres];
	    for(i = 1; i <= NumRelators; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
			if(Relators[i] == NULL) Mem_Error();
			q = *Relators[i];    
			p = *SUR[ReadPres][i];
			while( (*q++ = *p++) ) ;
			}
		NumPresChecked ++;
		i = Genus3ET(ReadPres + 1,MyCompNum,F1);
		if(i) 
			{
			FoundEssentialTorus = TRUE;
			return(n);
			}
		}
	return(n);		
}

int Genus3ET(int OrbitNum,int MyCompNum,char F1)
{
	unsigned char	*p,
					GenA,
					GenB,
					GenC,
					NumGens,
					x;
					
	int				i;
	
	/* Check if the Component "MyCompNum" has Boundary. */
					
	if(CBC[MyCompNum][0] == BDRY_UNKNOWN) return(0);
	for(i = 1; CBC[MyCompNum][i] < BDRY_UNKNOWN; i++) if(CBC[MyCompNum][i]) return(0);
	
	/*	The Component "MyCompNum" is closed. */
	
	for(i = 1; i <= 3; i++)
		{
		NumGens = 0;
		GenA = GenB = GenC = FALSE;
		p = *Relators[i];
		while((x = *p++)) 
			{
			switch(x)
				{
				case 'A':
				case 'a':
					if(GenA == FALSE)
						{
						GenA = TRUE;
						NumGens ++;
						}
					break;
				case 'B':
				case 'b':
					if(GenB == FALSE)
						{
						GenB = TRUE;
						NumGens ++;
						}			
					break;
				case 'C':
				case 'c':
					if(GenC == FALSE)
						{
						GenC = TRUE;
						NumGens ++;
						}
				}
			if(NumGens >= 3) break;	
			}
		if(NumGens < 3) 
			{
			if(GenA == FALSE) x = 'A';
			if(GenB == FALSE) x = 'B';
			if(GenC == FALSE) x = 'C';
			if(CheckDualRelator(x,MyCompNum)) return(0);
			if(Batch == FALSE)
				{
				if(GenA == FALSE) return(10*i + 1);
				if(GenB == FALSE) return(10*i + 2);
				if(GenC == FALSE) return(10*i + 3);
				}
			if(F1 || Batch == 10 || Batch == 11)
				{
				printf("\n\nThere is an essential torus in the manifold of Presentation %d Length %lu.",OrbitNum, SURL[OrbitNum - 1]);			
				printf("\nR%d is disjoint from cutting disk D_%c of the underlying handlebody H.",i,x);
				printf("\nIf h = H - D_%c and h' = H' - D_R%d, then T = Bdry h[R%d] = Bdry h'[Bdry D_%c] is an essential torus."
				,x,i,i,x);
				printf("\nR1 = %s",(char *) *Relators[1]);
				printf("\nR2 = %s",(char *) *Relators[2]);
				printf("\nR3 = %s",(char *) *Relators[3]);
				printf("\nBdry D_%c = %s",x,(char *) SETR4[MyCompNum]);
				Stow_ET_Data(MyCompNum,50,0,i,x,0,0,0,0,0,0);
				return(1);
				}	
			}
		continue;	
		}
	return(0);								
}	

int CheckDualRelator(char MissingGen,int MyCompNum)
{
	unsigned char	h,
					*p,
					*q,
					**Temp;
	
	int 			i;
	
	/***************************************************************************************************** 
		This routine checks if the DualRelator corresponding to the missing generator of Genus3ET()
	   	has less than full rank. It returns 0 if the dual relator has full rank and returns 1 otherwise. 
	******************************************************************************************************/
	
	NumGenerators = NumRelators = 3;
	Vertices = 6;
	Fill_A(NumRelators);				
	if(ComputeValences_A()) return(1);
	Get_Matrix();
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;
	if(Connected_(0,0) == FALSE) return(1);
	if(Sep_Pairs(0,0,1)) return(1);
	if(Planar(FALSE,TRUE) == TRUE) return(1);
	if(Diagram_Main()) return(1);
	
	h = MissingGen - 'A' + 1;
	Temp = Relators[1];
	Relators[1] = DualRelators[h];
	DualRelators[h] = Temp;
	
	/* Save a copy of our DualRelator in SETR4[MyCompNum]. */
	
	if(SETR4[MyCompNum] != NULL) DisposePtr((char **) SETR4[MyCompNum]);
	SETR4[MyCompNum] = (unsigned char *) NewPtr(GetHandleSize((char **) Relators[1]));
	if(SETR4[MyCompNum] == NULL) Mem_Error();
	q = SETR4[MyCompNum];
	p = *Relators[1];
	while( (*q++ = *p++) ) ;
	i = CheckPrimitivity();
	Temp = Relators[1];
	Relators[1] = DualRelators[h];
	DualRelators[h] = Temp;	
	if(i)
		{
		DisposePtr((char **) SETR4[MyCompNum]);
		SETR4[MyCompNum] = NULL;
		return(1);
		}
	return(0);
}

