#include "Heegaard.h"
#include "Heegaard_Dec.h"

/******************************* Functions in Heegaard25.c ********************************	
L  11 	Check_for_Big_SF(int MyHS,int MyOrbit,unsigned int MyOrbitLength)
L 675	Get_2_Gen_SF_EXPS1(unsigned char j)
L 812	Get_Gen_SF_EXPS2(unsigned char j,int* EXP1,int* EXP2,int* NEXP1,int* NEXP2)
L 978	Rewrite_Orbit_Reps2(int MyHS,int MyOrbit,unsigned int MyOrbitLength)
******************************************************************************************/

int Check_for_Big_SF(int MyHS,int MyOrbit,unsigned int MyOrbitLength)
{
	char			*CC = NULL;
	
    unsigned char	BadRel,
    				BadRelators,
    				FoundNew,
    				GensInRel[MAXNUMRELATORS + 1],
    				MyError = FALSE,
    				NumCommutators,
    				NumRegCommutators,
    				NumExceptionalFibers,
    				RFGen,
    				*RFL = NULL,
    				SFGenus,
					X,
					x,
					Y,
					y,
					z,
					*p,
					*q;
					
	int				*EXP1 =  NULL,
					*EXP2 =  NULL,
					*NEXP1 = NULL,
					*NEXP2 = NULL,
					TrialBeta;
					
	long int		e,
					e1,
					e2;				
                            
	unsigned int    C[125],
					i,
					j,
					k;
					
	unsigned long   HS,
					AlphasBetasSum,
					AlphasProduct,
					TorsionProduct;
					
	ldiv_t			qq;							
					
	/**********************************************************************************************
		Check_for_Big_SF() recognizes that certain pseudo-minimal presentations are presentations
		of vertical Heegaard splittings of closed, orientable Seifert-fibered spaces over closed,
		orientable surfaces.
	***********************************************************************************************/
	
	/**********************************************************************************************
		Count the number of generators that appear in each relator, there should be at most one
		relator containing more than two generators. Every other relator must either contain just
		two generators, say X and Y, and be of the form X^mY^n, X ≠ Y, m,n > 1; be a commutator 
		of the form X^mYx^my, m >= 1; or have only X^m, Y^n and Y^(n + 1) appear, m > 1.
	***********************************************************************************************/
	
	for(i = 0; i <= NumGenerators; i++) Alphas[i] = Betas[i] = 0;
	BadRelators = NumExceptionalFibers = NumRegCommutators = NumCommutators = 0;
	for(i = 1; i <= NumRelators; i++)
		{
		for(x = 'A',y = 'a'; x < 'A' + NumGenerators; x++,y++) C[x] = C[y] = 0;
		p = *Relators[i];
		while( (z = *p++) ) C[z]++;
		for(x = 'A',y = 'a',j = 0; x < 'A' + NumGenerators; x++,y++) 
			{
			if(C[x]) j++;
			if(C[y]) j++;
			}
		GensInRel[i] = j;
		if(j < 2) return(10); /* Relator[i] is either empty, a primitive, or a proper power. */
		if(j > 4)
			{
			if(++BadRelators > 1) return(11);
			BadRel = i;
			continue;
			}		
		HS = GetHandleSize((char **) Relators[i]);
		p = *Relators[i];
		q = p + HS - 2;
		X = *p;
		if(X > 94) X -= 32;
		x = X + 32;
		Y = *q;
		if(Y > 94) Y -= 32;
		y = Y + 32;		
		if(j == 2)
			{
			if(Get_2_Gen_SF_EXPS1(i)) return(12);
			if(NumAEXPS > 1 && NumBEXPS > 1) return(13);
			if(NumAEXPS == 1 && NumBEXPS == 1)
				{
				if(abs(EXPA1_SF[0]) == 1) return(14);
				if(abs(EXPB1_SF[0]) == 1) return(15);
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = abs(EXPA1_SF[0]);
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != abs(EXPA1_SF[0])) return(16);	
				if(Alphas[Y - 64] == 0) 
					{
					Alphas[Y - 64] = abs(EXPB1_SF[0]);
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != abs(EXPB1_SF[0])) return(17);				
				}
			if(NumAEXPS == 1 && NumBEXPS == 2)
				{
				if(abs(EXPA1_SF[0]) == 1) return(18);
				if(abs(EXPB1_SF[0] - EXPB1_SF[1]) != 1) return(19);
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = abs(EXPA1_SF[0]);
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != abs(EXPA1_SF[0])) return(20);
				if(Alphas[Y - 64] == 0) 
					{
					Alphas[Y - 64] = C[Y] + C[y];
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != (C[Y] + C[y])) return(21);
				
				/* Need to compute a trial Betas[Y - 64] */
				
				TrialBeta = NEXA1_SF[0];
				if(Betas[Y - 64] == 0) Betas[Y - 64] = TrialBeta;
				if(Betas[Y - 64] != TrialBeta) return(22);												
				}
			if(NumAEXPS == 2 && NumBEXPS == 1)
				{
				if(abs(EXPB1_SF[0]) == 1) return(23);
				if(abs(EXPA1_SF[0] - EXPA1_SF[1]) != 1) return(24);
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = C[X] + C[x];
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != (C[X] + C[x])) return(25);
				if(Alphas[Y - 64] == 0) 
					{
					Alphas[Y - 64] = abs(EXPB1_SF[0]);
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != abs(EXPB1_SF[0])) return(26);
				
				/* Need to compute a trial Betas[X - 64] */
				
				TrialBeta = NEXB1_SF[0];
				if(Betas[X - 64] == 0) Betas[X - 64] = TrialBeta;
				if(Betas[X - 64] != TrialBeta) return(27);						
				}
			}
		if(j == 3)
			{
			if(!((C[X] && C[x]) || (C[Y] && C[y])))
				{
				if(++BadRelators > 1) return(28);
				BadRel = i;
				continue;
				}			
			if(Get_2_Gen_SF_EXPS1(i)) return(29);
			if((C[X] && C[x]))
				{
				if((NumBEXPS > 1) || (abs(EXPB1_SF[0]) > 1))
					{
					if(++BadRelators > 1) return(30);
					BadRel = i;
					continue;
					}
				if(abs(EXPB1_SF[0]) == 1) return(300);					
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = abs(EXPA1_SF[0] - EXPA1_SF[1]);
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != abs(EXPA1_SF[0] - EXPA1_SF[1])) return(31);	
				if(Alphas[Y - 64] == 0)
					{
					Alphas[Y - 64] = C[Y] + C[y];
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != (C[Y] + C[y])) return(32);
				
				/* Need to compute a trial Betas[Y - 64] */
				
				TrialBeta = NEXA1_SF[0];
				if(NEXA1_SF[1] < TrialBeta) TrialBeta = NEXA1_SF[1];
				if(Betas[Y - 64] == 0) Betas[Y - 64] = TrialBeta;
				if(Betas[Y - 64] != TrialBeta) return(33);					
				}
			if((C[Y] && C[y]))
				{
				if((NumAEXPS > 1) || (abs(EXPA1_SF[0]) > 1))
					{
					if(++BadRelators > 1) return(34);
					BadRel = i;
					continue;
					}
				if(abs(EXPA1_SF[0]) == 1) return(340);					
				if(Alphas[Y - 64] == 0) 
					{
					Alphas[Y - 64] = abs(EXPB1_SF[0] - EXPB1_SF[1]);
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != abs(EXPB1_SF[0] - EXPB1_SF[1])) return(35);	
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = C[X] + C[x];
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != (C[X] + C[x])) return(36);
				
				/* Need to compute a trial Betas[X - 64] */
				
				TrialBeta = NEXB1_SF[0];
				if(NEXB1_SF[1] < TrialBeta) TrialBeta = NEXB1_SF[1];
				if(Betas[X - 64] == 0) Betas[X - 64] = TrialBeta;
				if(Betas[X - 64] != TrialBeta) return(37);					
				}				
			}
		if(j == 4) /* Check if Relator[i] is a commutator of the form X^mYx^my, m > 1. */
			{
			if((C[X] != C[x]) || (C[Y] != C[y]))
				{
				if(++BadRelators > 1) return(38);
				BadRel = i;
				continue;
				}
			if(C[X] > 1 && C[Y] > 1)
				{
				if(++BadRelators > 1) return(39);
				BadRel = i;
				continue;
				}
			if(C[X] == 1 && C[Y] == 1) /* There may be no more than one exceptional fiber. */
				{
				if(NumExceptionalFibers) return(40);
				if(Alphas[X - 64] == 0) Alphas[X - 64] = C[X];
				if(Alphas[X - 64] != C[X]) return(41);
				if(Alphas[Y - 64] == 0) Alphas[Y - 64] = C[Y];
				if(Alphas[Y - 64] != C[Y]) return(42);
				NumRegCommutators ++;				
				NumCommutators ++;
				if(NumRegCommutators == 1)
					{
					RFL = (unsigned char *)NewPtr(NumGenerators + 1);
					if(RFL == NULL) Mem_Error();
					for(k = 1; k <= NumGenerators; k++) RFL[k] = TRUE;
					}
				for(k = 1; k <= NumGenerators; k++) if((k != X - 64) && (k != Y - 64)) RFL[k] = FALSE; 	
				}
			if(C[X] > 1 && C[Y] == 1) /* Relators[i] is a oommutator of the desired form. */
				{
				if(Alphas[X - 64] == 0) 
					{
					Alphas[X - 64] = C[X];
					NumExceptionalFibers ++;
					}
				if(Alphas[X - 64] != C[X]) return(43);
				if(Alphas[Y - 64] == 0) Alphas[Y - 64] = C[Y];
				if(Alphas[Y - 64] != C[Y]) return(44);				
				NumCommutators ++;
				}				
			if(C[X] == 1 && C[Y] > 1) /* Relators[i] is a oommutator of the desired form. */
				{
				if(Alphas[X - 64] == 0) Alphas[X - 64] = C[X];
				if(Alphas[X - 64] != C[X]) return(43);
				if(Alphas[Y - 64] == 0) 
					{
					Alphas[Y - 64] = C[Y];
					NumExceptionalFibers ++;
					}
				if(Alphas[Y - 64] != C[Y]) return(44);				
				NumCommutators ++;
				}							
			}
		}
		
	/* Check that only one of NumRegCommutators and NumExceptionalFibers is nonzero. */
	
	if(NumRegCommutators && NumExceptionalFibers) return(45);
		
	/* Check if the number of commutators is even. */
	
	if(NumCommutators % 2) return(46);
	SFGenus = NumCommutators / 2;
	
	if(NumRegCommutators) 
		/* Check that there is exactly one generator which commutes with each of the other generators.
		Make RFGen that generator. It represents the regular fiber. (If such exists.) */
		{
		for(i = 1, j = 0; i <= NumGenerators; i++) if(RFL[i])
			{
			RFGen = i;
			j++;
			}
		if(j != 1) 
			{
			MyError = 70;
			goto END;
			}
		for(i = 1, BadRelators = 0; i <= NumRelators; i++) if(GensInRel[i] > 4)
			{
			if(++BadRelators > 1)
				{
				MyError = 71;
				goto END;				
				}
			BadRel = i;				
			}
		if(BadRelators != 1)
			{
			MyError = 72;
			goto END;
			}						
		}
		
	/* Check that each generator appears in Alphas[ ] with nonzero exponent. */
	
	for(i = 1; i <= NumGenerators; i++) if(Alphas[i] == 0) return(47);
	
	if(NumExceptionalFibers)
		{
		/* Arrange generators with Alphas > 1 into bipartite form so Betas can be computed. */
	
		CC = (char *) NewPtr(NumGenerators + 1);
		if(CC == NULL) Mem_Error();
		for(i = 0; i <= NumGenerators; i++) CC[i] = 0;
		for(i = 1; i <= NumGenerators; i++) if(Alphas[i] > 1)
			{
			CC[i] = 1;
			break;
			}
		j = 1;
		do
			{
			for(i = 1,FoundNew = FALSE; i <= NumRelators; i++)
				{
				if(GensInRel[i] > 3) continue;
				if(i == BadRel) continue;
				HS = GetHandleSize((char **) Relators[i]);
				p = *Relators[i];
				q = p + HS - 2;
				X = x = *p;
				if(X > 94) X -= 96;
				else X -= 64;
				Y = y = *q;
				if(Y > 94) Y -= 96;
				else Y -= 64;	
				if(CC[X] && CC[Y]) continue;
				if(!CC[X] && !CC[Y]) continue;
				if(CC[X] && !CC[Y])
					{
					if((x < 94 && y > 94) || (x > 94 && y < 94))
						CC[Y] = CC[X];
					else
						CC[Y] = -CC[X];	
					}
				if(!CC[X] && CC[Y])
					{
					if((x < 94 && y > 94) || (x > 94 && y < 94))
						CC[X] = CC[Y];
					else
						CC[X] = -CC[Y];					
					}
				FoundNew = TRUE;
				if(++j == (NumGenerators - NumCommutators)) break;	
				}		
			}
		while(FoundNew == TRUE);
	
		if(j != (NumGenerators - NumCommutators)) 
			{
			MyError = 48;
			goto END;
			}
		}
		
	if(BadRelators)
		{
		EXP1 = (int*) NewPtr(sizeof(int)*(NumGenerators + 1));
		if(EXP1 == NULL) Mem_Error();		
		EXP2 = (int*) NewPtr(sizeof(int)*(NumGenerators + 1));
		if(EXP2 == NULL) Mem_Error();
		NEXP1 = (int*) NewPtr(sizeof(int)*(NumGenerators + 1));
		if(NEXP1 == NULL) Mem_Error();
		NEXP2 = (int*) NewPtr(sizeof(int)*(NumGenerators + 1));
		if(NEXP2 == NULL) Mem_Error();
		j = Get_Gen_SF_EXPS2(BadRel,EXP1,EXP2,NEXP1,NEXP2);
		if(j) 
			{
			MyError = j;			
			goto END;
			}	
		}	
		
	if(BadRelators)
		{
		/* Check the form of the "BadRelator". There should be at most one 'non-commutator' generator 
		which appears in the "BadRelator" with more than one exponent.	*/
		
		for(i = 1,j = 0; i <= NumGenerators; i++) if(EXP2[i] != 0) j++;
		if(j > NumCommutators + 1) 
			{		
			MyError = 49;
			goto END;
			}
		
		/* If j == NumCommutators, the "BadRelator" does not add another exceptional fiber. 
		Check that NEXP1[i] is either 0 or 1 for each generator. */
		
		if(j == NumCommutators) for(i = 1; i <= NumGenerators; i++) if(NEXP1[i] > 1) 
			{			
			MyError = 50;
			goto END;
			}
		
		for(i = 1,j = 0; i <= NumGenerators; i++) if(NEXP1[i] > j) j = NEXP1[i];
		for(i = 1; i <= NumGenerators; i++) if(NEXP1[i] && (NEXP1[i] != j) && (NEXP1[i] + NEXP2[i] != j)) 
			{
			MyError = 51;
			goto END;
			}
		
		if(NumRegCommutators)	/* Compute Alphas[0] and Betas[0]. */
			{
			Alphas[0] = j;
			for(i = 1; i <= NumGenerators; i++) if(NEXP2[i] && (NEXP1[i] + NEXP2[i] == Alphas[0]))
				{
				if(EXP1[i] > EXP2[i]) 
					Betas[0] = NEXP1[i];
				else 
					Betas[0] = NEXP2[i];
				break;
				}
			if(Alphas[0] > 1 && i != RFGen)
				{
				MyError = 73;
				goto END;
				}			
			}
		
		if(NumExceptionalFibers)
			{
			/* Compute Betas[i] when Alphas[i] > 1. */
		
			for(i = 1; i <= NumGenerators; i++) if(Alphas[i] > 1)
				{
				if(Betas[i] && EXP1[i] == -1 && EXP2[i] == 0) Betas[i] = Alphas[i] - Betas[i];
				if(Betas[i] == 0)
					{
					if(EXP1[i] > 0) 
						Betas[i] = EXP1[i] % Alphas[i];
					else
						{
						Betas[i] = -EXP1[i];
						Betas[i] = Betas[i] % Alphas[i];
						Betas[i] = Alphas[i] - Betas[i];
						}	
					}
				if(CC[i] == -1) Betas[i] = Alphas[i] - Betas[i];				
				}
			
			/* Compute Alphas[0] and Betas[0]. */
			
			if(NumExceptionalFibers > 1) 
				{
				for(i = 1,j = 0; i <= NumGenerators; i++) if(Alphas[i] > 1 && NEXP1[i] > j) j = NEXP1[i];
				Alphas[0] = j;
				}
			if(NumExceptionalFibers == 1)
				{
				for(i = 1; i <= NumGenerators; i++) if(Alphas[i] > 1)
				Alphas[0] = NEXP1[i] + NEXP2[i];
				}
			for(i = 1; i <= NumGenerators; i++) if(NEXP2[i] && (NEXP1[i] + NEXP2[i] == Alphas[0]))
				{
				if(EXP1[i] > EXP2[i]) 
					Betas[0] = NEXP1[i];
				else 
					Betas[0] = NEXP2[i];
				if(CC[i] == -1) Betas[0] = Alphas[0] - Betas[0];
				break;
				}
			}
		}
		
		/* Compute the Euler number e. */
		
		TorsionProduct = Compute_Homology(TRUE);
		
		for(i = 0,AlphasBetasSum = 0; i <= NumGenerators; i++)
			{
			AlphasProduct = Betas[i];
			for(j = 0; j <= NumGenerators; j++)
				{
				if(j == i) continue;
				AlphasProduct *= Alphas[j];
				}
			AlphasBetasSum += AlphasProduct;
			}
								
		for(i = NumExceptionalFibers = 0,AlphasProduct = 1; i <= NumGenerators; i++) if(Alphas[i] > 1)
			{
			NumExceptionalFibers ++;
			AlphasProduct *= Alphas[i];
			}
	
		if(AlphasProduct == 0)
			{
			MyError = 52;
			goto END;
			}
	
		k = 0;		
		qq = ldiv(AlphasBetasSum + TorsionProduct, AlphasProduct);
		if(qq.rem == 0) 
			{
			e1 = qq.quot;
			k += 1;
			}
		qq = ldiv(AlphasBetasSum - TorsionProduct, AlphasProduct);
		if(qq.rem == 0) 
			{
			e2 = qq.quot;
			k += 2;
			}
			
		switch(k)
			{
			case 0:
				MyError = 53;
				goto END;
			case 1:
				e = e1;
				break;
			case 2:
				e = e2;
				break;
			case 3:
				break;	
			}
/*		
	printf("\n");
	for(i = 0; i <= NumGenerators; i++)
		printf("Alpha[%u] = %2d ",i,Alphas[i]);
	printf("\n");	
	for(i = 0; i <= NumGenerators; i++)
		printf(" Beta[%u] = %2d ",i,Betas[i]);
	printf("\n");	
	for(i = 0; i <= NumGenerators; i++)
		printf(" EXP1[%u] = %2d ",i,EXP1[i]);
	printf("\n");	
	for(i = 0; i <= NumGenerators; i++)
		printf("NEXP1[%u] = %2d ",i,NEXP1[i]);	
	printf("\n");	
	for(i = 0; i <= NumGenerators; i++)
		printf(" EXP2[%u] = %2d ",i,EXP2[i]);
	printf("\n");	
	for(i = 0; i <= NumGenerators; i++)
		printf("NEXP2[%u] = %2d ",i,NEXP2[i]);
	if(CC)
		{	
		printf("\n");	
		for(i = 0; i <= NumGenerators; i++)
			printf("CC[%u] = %2d ",i,CC[i]);
		}
*/	
	/* Sort the Alphas[ ] and Betas [ ] by increasing Alphas[ ] and increasing Betas[ ]. */
	
	do
		{
		for(i = j = 0; i < NumGenerators; i++) 
			{
			if((Alphas[i] > Alphas[i + 1]) || (Alphas[i] == Alphas[i + 1] && Betas[i] > Betas[i + 1]))
				{
				j = Alphas[i];
				Alphas[i] = Alphas[i + 1];
				Alphas[i + 1] = j;				
				j = Betas[i];
				Betas[i] = Betas[i + 1];
				Betas[i + 1] = j;
				j = 1;
				}
			}
		}
	while(j > 0);	
	
	Rewrite_Orbit_Reps2(MyHS,MyOrbit,MyOrbitLength);

	if(k < 3)
		{	
		FoundBigSF = TRUE;
		printf("\n\n Mfld = SF( %d, %ld | ",SFGenus,e);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Betas[i],Alphas[i]);
		printf(") OR ");	
		printf("SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
		printf(")");
		if(H_Results != NULL)
			{
			fprintf(H_Results," SF( %d, %ld | ",SFGenus,e);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Betas[i],Alphas[i]);
			fprintf(H_Results,") OR ");	
			fprintf(H_Results," SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
			fprintf(H_Results,")");			
			}
		}
	if(k == 3)
		{
		FoundBigSF = TRUE;
		printf("\n\nThere is an Euler number ambiguity! Either:");
		printf("\nMfld = SF( %d, %ld | ",SFGenus,e1);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Betas[i],Alphas[i]);
		printf(") OR ");	
		printf("SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e1);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
		printf(")");	
		printf("\nOr perhaps:");
		printf("\nMfld = SF( %d, %ld | ",SFGenus,e2);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Betas[i],Alphas[i]);
		printf(") OR ");	
		printf("SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e2);
		for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) printf("%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
		printf(")");
		if(H_Results != NULL)
			{
			fprintf(H_Results," There is an Euler number ambiguity! Either:");
			fprintf(H_Results,"\nSF( %d, %ld | ",SFGenus,e1);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Betas[i],Alphas[i]);
			fprintf(H_Results,") OR ");	
			fprintf(H_Results," SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e1);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
			fprintf(H_Results,")");	
			fprintf(H_Results,"\nOr perhaps:");
			fprintf(H_Results,"\nSF( %d, %ld | ",SFGenus,e2);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Betas[i],Alphas[i]);
			fprintf(H_Results,") OR ");	
			fprintf(H_Results,"SF( %d, %ld | ",SFGenus,NumExceptionalFibers - e2);
			for(i = 0; i <= NumGenerators; i++) if(Alphas[i] > 1) fprintf(H_Results,"%d/%d ",Alphas[i]-Betas[i],Alphas[i]);
			fprintf(H_Results,")");			
			}		
		}	
		
END:

	if(CC)			DisposePtr((char *) CC);
	if(RFL)			DisposePtr((unsigned char *) RFL);
	if(BadRelators)
		{
		if(EXP1)  		DisposePtr((int*) EXP1);
		if(EXP2)  		DisposePtr((int*) EXP2);
		if(NEXP1) 		DisposePtr((int*) NEXP1);
		if(NEXP2) 		DisposePtr((int*) NEXP2);
		}

	if(MyError) return(MyError);		
	return(0);			
}

int Get_2_Gen_SF_EXPS1(unsigned char j)
{
    /*********************************************************************************************
        This routine determines the exponents with which each generator appears in Relators[j].
    These exponents are left in the arrays EXPA1_SF[] and EXPB1_SF[]. The routine also counts
    the number of times each exponent of each generator appears in Relators[j], and saves these
    values in the arrays NEXA1_SF[] and NEXB1_SF[]. 
    	If Relators[j] has minimal length and Relators[j] is an SF relator, then no generator
    can appear in Relators[j] with more than 2 exponents. (Note exponents are signed here, so 
    e and -e are different exponents.)
    *********************************************************************************************/    
    						
	unsigned char  	i,
					*p,
					x,
					y,
					Z,
					z;
						
	int   			ex,
					sex,
					*q,
					*r;
    
    if(GetHandleSize((char**) Relators[j]) < 3) return(1);  /* Relators[j] is either empty, or a primitive! */
                           
    for(i = 0; i < 3; i++) NEXA1_SF[i] = NEXB1_SF[i] = EXPA1_SF[i] = EXPB1_SF[i] = 0;
	
	p = *Relators[j];
	x = *p++;
	if(!x) return(2);			/* Relators[j] is empty!  */
	Z = x;
	if(Z > 96) 
		{
		z = Z;
		Z = z - 32;
		}
	else z = Z + 32;
	ex = 1;
	while(*p == x)
		{
		ex++;
		p++;
		}
	sex = ex;
	ex = 0;
	if(*p) x = *p;
	else return(3); 			/* Relators[j] is a proper power!  */
	while( (y = *p++) )
		{
		if(x == y)
			ex++;
		else
			{
			if(x == Z || x == z) 
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
			for(x = 0; x < 2 && ex != q[x] && q[x]; x++) ;
			if(x == 2) return(4);							/* Not 2 Gen SF! */
			q[x] = ex;
			r[x]++;
			ex = 1;    
			}
		x = y;
		}
	y = **Relators[j];        
	if(x == y)
		{
		if(x == Z || x == z) 
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
		for(x = 0; x < 2 && ex != q[x] && q[x]; x++) ;
		if(x == 2) return(5);							/* Not 2 Gen SF! */
		q[x] = ex;
		r[x]++;
		}
	else
		{
		if(x == Z || x == z) 
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
		for(x = 0; x < 2 && ex != q[x] && q[x]; x++) ;
		if(x == 2) return(6);							/* Not 2 Gen SF! */
		q[x] = ex;
		r[x]++;
		
		ex = sex;
		x = y;
		
		if(x == Z || x == z) 
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
		for(x = 0; x < 2 && ex != q[x] && q[x]; x++) ;
		if(x == 2) return(7);							/* Not 2 Gen SF! */
		q[x] = ex;
		r[x]++;
		}
    
    for(i = NumAEXPS = 0; i < 3; i++) if(EXPA1_SF[i]) NumAEXPS ++;
    for(i = NumBEXPS = 0; i < 3; i++) if(EXPB1_SF[i]) NumBEXPS ++;
    
    return(0);            
}

int Get_Gen_SF_EXPS2(unsigned char j,int* EXP1,int* EXP2,int* NEXP1,int* NEXP2)
{
    /*********************************************************************************************
        This routine determines the exponents with which each generator appears in Relators[j].
    These exponents are left in the arrays EXP1[] and EXP2[]. The routine also counts the
    number of times each exponent of each generator appears in Relators[j], and saves these
    values in the arrays NEXP1[] and NEXP2[]. 
    	If Relators[j] has minimal length and Relators[j] is an SF relator, then no generator
    can appear in Relators[j] with more than 2 exponents. (Note exponents are signed here, so 
    e and -e are different exponents.)
    *********************************************************************************************/    
    						
	unsigned char  	i,
					*p,
					x,
					y,
					Z;
						
	int   			ex,
					sex;
    
    if(GetHandleSize((char**) Relators[j]) < 3) return(1);  /* Relators[j] is either empty, or a primitive! */
                           
    for(i = 0; i <= NumGenerators; i++) NEXP1[i] = NEXP2[i] = EXP1[i] = EXP2[i] = 0;
	
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
	else return(3); 			/* Relators[j] is a proper power!  */
	while( (y = *p++) )
		{
		if(x == y)
			ex++;
		else
			{
			if(x > 96) ex = -ex;
			Z = x;
			if(Z > 96) 
				Z -= 96;
			else 
				Z -= 64;
			if(EXP1[Z] && EXP2[Z])
				{
				if(ex == EXP1[Z]) NEXP1[Z] ++;
				if(ex == EXP2[Z]) NEXP2[Z] ++;
				if(ex != EXP1[Z] && ex != EXP2[Z]) return(4); 	/* Not SF! */
				}
			if(EXP1[Z] && !EXP2[Z])
				{
				if(ex == EXP1[Z]) NEXP1[Z] ++;
				if(ex != EXP1[Z]) 
					{
					EXP2[Z] = ex;
					NEXP2[Z] ++;
					}
				}			
			if(!EXP1[Z])
				{
				EXP1[Z] = ex;
				NEXP1[Z] ++;				
				}			
			ex = 1;   
			}
		x = y;
		}
	y = **Relators[j];        
	if(x == y)
		{
		ex += sex;	
		if(x > 96) ex = -ex;
		Z = x;
		if(Z > 96) 
			Z -= 96;
		else 
			Z -= 64;	
		if(EXP1[Z] && EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex == EXP2[Z]) NEXP2[Z] ++;
			if(ex != EXP1[Z] && ex != EXP2[Z]) return(4); 	/* Not SF! */
			}
		if(EXP1[Z] && !EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex != EXP1[Z]) 
				{
				EXP2[Z] = ex;
				NEXP2[Z] ++;
				}
			}			
		if(!EXP1[Z])
			{
			EXP1[Z] = ex;
			NEXP1[Z] ++;				
			}
		}
	else
		{
		if(x > 96) ex = -ex;
		Z = x;
		if(Z > 96) 
			Z -= 96;
		else 
			Z -= 64;		
		if(EXP1[Z] && EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex == EXP2[Z]) NEXP2[Z] ++;
			if(ex != EXP1[Z] && ex != EXP2[Z]) return(4); 	/* Not SF! */
			}
		if(EXP1[Z] && !EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex != EXP1[Z]) 
				{
				EXP2[Z] = ex;
				NEXP2[Z] ++;
				}
			}			
		if(!EXP1[Z])
			{
			EXP1[Z] = ex;
			NEXP1[Z] ++;				
			}		
		ex = sex;
		x = y;
		if(x > 96) ex = -ex;
		Z = x;
		if(Z > 96) 
			Z -= 96;
		else 
			Z -= 64;		
		if(EXP1[Z] && EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex == EXP2[Z]) NEXP2[Z] ++;
			if(ex != EXP1[Z] && ex != EXP2[Z]) return(4); 	/* Not SF! */
			}
		if(EXP1[Z] && !EXP2[Z])
			{
			if(ex == EXP1[Z]) NEXP1[Z] ++;
			if(ex != EXP1[Z]) 
				{
				EXP2[Z] = ex;
				NEXP2[Z] ++;
				}
			}			
		if(!EXP1[Z])
			{
			EXP1[Z] = ex;
			NEXP1[Z] ++;				
			}
		}
    
    return(0);            
}

int Rewrite_Orbit_Reps2(int MyHS,int MyOrbit,unsigned int MyOrbitLength)
{	
	unsigned char 	*p,
					x,
					y;

	unsigned int	ex,
					i;
	
    printf("\n\nRep of Orbit %d of HS %d, Gen %d, Rel %d, Length %u:",MyOrbit,MyHS + 1,
    NumGenerators,NumRelators,MyOrbitLength );
	for(i = 1; i <= NumRelators; i++)
		{
		printf("\n");
		p = *Relators[i];
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
		
	return(0);		
}