#include "Heegaard.h"
#include "Heegaard_Dec.h"

/******************************* Functions in Heegaard28.c ********************************	
L 2582 Check_C_Robustness(char Flag1,char Flag2)
L  967 Check_R1_Positivity(void)
L  852 FindMinExpAndContext(char WhichGen, unsigned int MinExp)
L   32 Genus_Two_One_Relator_Annuli_And_Tori(char F1)
L  304 Genus_Two_One_Relator_Annuli_And_Tori_S1(char Print)
L  518 Genus_Two_One_Relator_Annuli_And_Tori_S2(unsigned int ZZ0,unsigned int ZZ1, unsigned int ZZ2,
	   unsigned int ZZ3, unsigned int Source, unsigned int NumReps,char F1,char Print)
L  561 Get_Genus_Two_Commutators(char Flag1,char Print)
L 1950 Get_Sep_Disk_Dual(char)
L 1434 Get_Universal_Minimizer_Waves(char F1)
L 1830 Get_Universal_Minimizer_Waves_S1(unsigned char NumWaveGuides)
L 1323 Init_Get_Universal_Minimizer_Waves(int NumHSReps,int* HSRepL)
L 3525 Look_For_Disjoint_Genus_2_Curves(char F1)
L 2758 Look_For_PP_SF_Curves(unsigned char NumWaveGuides,char F1,char F2)
L 2037 P_and_PP_Curves_Disjoint_From_Relators(char Flag2)
L 1201 Pos_Relator_Check_Do_Auts(unsigned int ZZ0,unsigned int ZZ1, unsigned int ZZ2,
	   unsigned int ZZ3, unsigned int Source, unsigned int NumReps)
L 1216 Pos_Relator_Check_Min_Exp(char Gen1,char Gen2,char Gen3,char Gen4)
L 1999 ReWrite_WaveGuides(unsigned char* MyWaveGuide)
L 2720 Save_P_or_PP(unsigned char** Str1,unsigned int HS)
L 3365 Set_Up_SF_Check(int NumStowed,unsigned char* NSL,unsigned int* NSEL,char F1,char F2)
L 3350 Stow_Relators(unsigned char* MyPtr,unsigned int HS,int i)
L 3496 Translate_2_Dual_Pres(unsigned char* MyPtr)
******************************************************************************************/

int		NumSaved;

int Genus_Two_One_Relator_Annuli_And_Tori(char F1,char Print)
{					
	unsigned char	i,
					NegExpLoc,
					NumNegAExps,
					NumNegBExps,
					NumPosAExps,
					NumPosBExps,
					PosExpLoc,
					*p,
					*q;

	int				GTCRV,
					GTS1RV,
					GTS2RV,
					SumAs,
					SumBs;
										
	unsigned int	Diff,
					MaxAExp,
					MaxBExp,
					MinExp;
					
	if((B10B11Recognized || Batch == 56) && H_Results == NULL) return(2);			
					
	if(F1)
		{
		if(NumRelators != 1) return(2);
		if(NumGenerators != 2) return(2);
		
		if(Find_Flow_A(NORMAL,0)) return(2);
		if(Length < 2) return(2);
		
		/* Save a copy of Relators[1] in Relators[3] before doing any level-transformations. */
	
		if(Relators[3] != NULL) DisposeHandle((char **) Relators[3]);
		Relators[3] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[1]));	
		if(Relators[3] == NULL) Mem_Error();
		p = *Relators[3];
		q = *Relators[1];
		while( (*p++ = *q++) ) ;
		}
	
	GTS1RV = Genus_Two_One_Relator_Annuli_And_Tori_S1(Print);				
	if(GTS1RV) return(GTS1RV);
	
	/******************************************************************************************* 	
		If R is disjoint from a proper-power or disjoint from a non-separating annulus, and
		Genus_Two_One_Relator_Annuli_And_Tori_S1( ) returned 0, then the only possibility is 
		that there exist level-transformations of R which convert R into a form in which
		Genus_Two_One_Relator_Annuli_And_Tori_S1( ) will return 1. So we check cases in which 
		R = Relators[1] has level-transformations which might transform R into a form in which 
		Genus_Two_One_Relator_Annuli_And_Tori_S1( ) will return 1.
	*******************************************************************************************/
	
	/*
		printf("\n\nA[0][1] %d, A[0][2] %d, A[0][3] %d, A[2][3] %d\n\n",A[0][1], A[0][2], A[0][3], A[2][3]);
		for(i = 0; i < 8; i++) printf(" EXPA1_SF[%d] = %3d",i,EXPA1_SF[i]);
		printf("\n");
		for(i = 0; i < 8; i++) printf(" NEXA1_SF[%d] = %3d",i,NEXA1_SF[i]);
		printf("\n");
		for(i = 0; i < 8; i++) printf(" EXPB1_SF[%d] = %3d",i,EXPB1_SF[i]);
		printf("\n");
		for(i = 0; i < 8; i++) printf(" NEXB1_SF[%d] = %3d",i,NEXB1_SF[i]);
		printf("\n");
	*/	

	Diff = abs(A[1][2] - A[1][3]);	
	
								/*** |A| = |B| recognition. ***/
	
	if(Diff == A[0][1] && Diff == A[2][3]) /*** V[0] == V[2] ***/
		{		
		for(i = SumAs = 0; NEXA1_SF[i] > 0 && i < 8; i++) SumAs += NEXA1_SF[i]*EXPA1_SF[i];
		for(i = SumBs = 0; NEXB1_SF[i] > 0 && i < 8; i++) SumBs += NEXB1_SF[i]*EXPB1_SF[i]; 
		
		if(abs(SumAs) != abs(SumBs))
			{			
			if(NEXA1_SF[1] == 0 && abs(EXPA1_SF[0]) == 1 && NEXB1_SF[2] == 0 && EXPB1_SF[0]*EXPB1_SF[1] == -1)
				/* 'A' appears only as A or as a, 'B' appears only as B and b. */
				/* Both A --> AB and A --> Ab are level-transformations. */
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,1,1,Print)) ) return(GTS2RV);
		
			if(NEXB1_SF[1] == 0 && abs(EXPB1_SF[0]) == 1 && NEXA1_SF[2] == 0 && EXPA1_SF[0]*EXPA1_SF[1] == -1)
				/* 'B' appears only as B or as b, 'A' appears only as A and a. */
				/* Both B --> BA and B --> Ba are level-transformations. */
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,0,1,2,Print)) ) return(GTS2RV);			
		
			if(NEXA1_SF[2] == 0 && EXPA1_SF[0]*EXPA1_SF[1] == 2) /* 'A' appears only as A and A^2 or as a and a^2. */
				{
				if(A[1][3] > 0 && A[1][3] < A[1][2]) /* A --> Ab is level. */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(1,0,0,1,2,1,3,Print)) ) return(GTS2RV);
				
				if(A[1][2] > 0 && A[1][2] < A[1][3]) /* A --> AB is level. */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,1,4,Print)) ) return(GTS2RV);
				}
			
			if(NEXB1_SF[2] == 0 && EXPB1_SF[0]*EXPB1_SF[1] == 2) /* 'B' appears only as B and B^2 or as b and b^2. */
				{
				if(B[3][1] > 0 && B[3][1] < B[3][0]) /* B --> Ba is level. */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,1,0,0,1,5,Print)) ) return(GTS2RV);
						
				if(B[3][0] > 0 && B[3][0] < B[3][1]) /* B --> BA is level. */				
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,0,1,6,Print)) ) return(GTS2RV);			
				}
			}
			
		if(abs(SumAs) == abs(SumBs))
			{	
			/******************************************************************************************
				If R is disjoint from a non-separating annulus whose bdry comps are primitives,
				and each generator does not appear in R only with exponents ±1, (which has already
				been checked), then each generator appears in R only with exponents e with |e| <= 2.
				Furthermore, each generator appears with exponent(s) of absolute value 2.
			******************************************************************************************/
			
			for(i = MaxAExp = 0; NEXA1_SF[i] > 0 && i < 8; i++) 
				if(abs(EXPA1_SF[i]) > MaxAExp) MaxAExp = abs(EXPA1_SF[i]);
			for(i = MaxBExp = 0; NEXB1_SF[i] > 0 && i < 8; i++) 
				if(abs(EXPB1_SF[i]) > MaxBExp) MaxBExp = abs(EXPB1_SF[i]);			
			if(MaxAExp == 2 && MaxBExp == 2)
				{
				if(A[1][3] > 0 && A[1][3] < A[1][2]) 
					/* A --> Ab is level. */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(1,0,0,1,2,1,7,Print)) ) return(GTS2RV);
				
				if(A[1][2] > 0 && A[1][2] < A[1][3]) 
					/* A --> AB is level. */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,1,8,Print)) ) return(GTS2RV);
				}
			}					
		}

								/*** |A| > |B| recognition. ***/
	
	if(Diff < A[0][1] && Diff == A[2][3]) ; /*** V[0] > V[2] ***/
		{
		if(NEXB1_SF[2] == 0 && EXPB1_SF[0]*EXPB1_SF[1] == -1)
			{
			/* 'B' appears only with exponents 1 and -1. */
			
			/* Find the minimum absolute value of 'A' exponents. */
			
			for(i = 0, MinExp = BIG_NUMBER; NEXA1_SF[i] > 0 && i < 8; i++) 
				if(abs(EXPA1_SF[i]) < MinExp) MinExp = abs(EXPA1_SF[i]);
				
			i = FindMinExpAndContext('B', MinExp);
			switch(i)
				{	
				case 1:
				case 4:		
					/* B --> Ba^(MinExp). */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,1,0,0,MinExp,13,Print)) ) return(GTS2RV);
					break;
				case 2:
				case 3:	
					/* B --> BA^(MinExp). */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,0,MinExp,14,Print)) ) return(GTS2RV);
					break;
				default:
					break;
				}
			}	
					
		if((NEXB1_SF[1] == 0 && abs(EXPB1_SF[0]) == 1) || (NEXB1_SF[2] == 0 && EXPB1_SF[0]*EXPB1_SF[1] == 2))
			{
			/* 	Case 'B' appears only with exponent 1, or only with exponent -1, 
				or only with exponents 1 and 2, or only with exponents -1 and -2. */
			
			for(i = NumNegAExps = NumPosAExps = 0; i < 8; i++)  
				{
				/* Count the number of positive and negative exponents with which 'A' appears. */
				if(EXPA1_SF[i] < 0) 
					{
					NumNegAExps ++;
					NegExpLoc = i;
					}
				if(EXPA1_SF[i] > 0) 
					{
					NumPosAExps ++;
					PosExpLoc = i;
					}
				}
				
			if(EXPB1_SF[0] >=  1  && NumNegAExps == 1) 	/* B --> BA^-EXPA1_SF[NegExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,0,-EXPA1_SF[NegExpLoc],9,Print)) ) return(GTS2RV);	
								
			if(EXPB1_SF[0] <= -1  && NumPosAExps == 1) 	/* B --> BA^ EXPA1_SF[PosExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,0,EXPA1_SF[PosExpLoc],10,Print)) ) return(GTS2RV);
									
			if(EXPB1_SF[0] >=  1  && NumPosAExps == 1 && NumNegAExps != 1)  /* B --> Ba^ EXPA1_SF[PosExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,1,0,0,EXPA1_SF[PosExpLoc],11,Print)) ) return(GTS2RV);			
												
			if(EXPB1_SF[0] <= -1  && NumNegAExps == 1 && NumPosAExps != 1) 	/* B --> Ba^-EXPA1_SF[NegExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,1,0,0,-EXPA1_SF[NegExpLoc],12,Print)) ) return(GTS2RV);			
			}
		}
	
								/*** |A| < |B| recognition. ***/
	
	if(Diff == A[0][1] && Diff < A[2][3]) ; /*** V[0] < V[2] ***/
		{
		if(NEXA1_SF[2] == 0 && EXPA1_SF[0]*EXPA1_SF[1] == -1)
			{
			/* Case in which 'A' appears only with exponents 1 and -1. */
			
			/* Find the minimum absolute value of 'B' exponents. */
			
			for(i = 0, MinExp = BIG_NUMBER; NEXB1_SF[i] > 0 && i < 8; i++) 
				if(abs(EXPB1_SF[i]) < MinExp) MinExp = abs(EXPB1_SF[i]);
				
			i = FindMinExpAndContext('A', MinExp);
			switch(i)
				{	
				case 1:
				case 4:	
					/* A --> Ab^(MinExp). */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(1,0,0,1,2,MinExp,19,Print)) ) return(GTS2RV);	
					break;
				case 2:
				case 3:	
					/* A --> AB^(MinExp). */
					if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,MinExp,20,Print)) ) return(GTS2RV);	
					break;
				default:
					break;
				}
			}
					
		if((NEXA1_SF[1] == 0 && abs(EXPA1_SF[0]) == 1) || (NEXA1_SF[2] == 0 && EXPA1_SF[0]*EXPA1_SF[1] == 2))
			{
			/* 	Case 'A' appears only with exponent 1, or only with exponent -1,
				or only with exponents 1 and 2, or only with exponents -1 and -2. */
			
			for(i = NumNegBExps = NumPosBExps = 0; i < 8; i++)
				{
				/* Count the number of positive and negative exponents with which 'B' appears. */
				if(EXPB1_SF[i] < 0) 
					{
					NumNegBExps ++;
					NegExpLoc = i;
					}
				if(EXPB1_SF[i] > 0) 
					{
					NumPosBExps ++;
					PosExpLoc = i;
					}
				}
				
			if(EXPA1_SF[0] >=  1  && NumNegBExps == 1)	/* A --> AB^-EXPB1_SF[NegExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,-EXPB1_SF[NegExpLoc],15,Print)) ) return(GTS2RV);
								
			if(EXPA1_SF[0] <= -1  && NumPosBExps == 1) 	/* A --> AB^ EXPB1_SF[PosExpLoc] */			
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(0,1,0,1,2,EXPB1_SF[PosExpLoc],16,Print)) ) return(GTS2RV);
									
			if(EXPA1_SF[0] >=  1  && NumPosBExps == 1 && NumNegBExps != 1)  /* A --> Ab^ EXPB1_SF[PosExpLoc] */
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(1,0,0,1,2,EXPB1_SF[PosExpLoc],17,Print)) ) return(GTS2RV);
												
			if(EXPA1_SF[0] <= -1  && NumNegBExps == 1 && NumPosBExps != 1) 	/* A --> Ab^-EXPB1_SF[NegExpLoc] */
				if( (GTS2RV = Genus_Two_One_Relator_Annuli_And_Tori_S2(1,0,0,1,2,-EXPB1_SF[NegExpLoc],18,Print)) ) return(GTS2RV);
			}
		}
		
	if(F1) 
		{
		GTCRV = Get_Genus_Two_Commutators(FALSE,Print);
		if(GTCRV) return(GTCRV);
		}
		
	return(0);
}

int Genus_Two_One_Relator_Annuli_And_Tori_S1(char Print)
{
	unsigned char	i;
	
	int				NumIntersections;
	
	/******************************************************************************************************	
		The first time Genus_Two_One_Relator_Annuli_And_Tori_S1() is called, it looks only at relator R. 
		If Genus_Two_One_Relator_Annuli_And_Tori_S1() does not return 1 after its first call, Heegaard 
		generates the four possible separating simple closed curves C1, C2, C3, and C4, disjoint from R, 
		which could be disjoint from a proper-power R' intersecting R more than once, or disjoint from 
		a non-separating annulus, with bdry component R' intersecting R more than once. 
			(Note in subsequent calls, Ci appears as R1; the original R as R2.)
	*******************************************************************************************************/
		
	if(Get_Genus_2_EXPS()) return(2);
	
	if(NEXA1_SF[2] == 0) 	/* 'A' appears with at most 2 exponents. */
		{
		if(NEXA1_SF[1] == 0 && (abs(EXPA1_SF[0]) > 1)) 	/* 'A' appears only as A^e, e > 1. */
			{
			if(!Print) return(1);
			printf("\n\nR = %s is disjoint from a proper-power A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
			if(B10B11Recognized || Batch == 56) fprintf(H_Results," R = %s is disjoint from a proper-power A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
			return(1);
			}
		if(abs(EXPA1_SF[0]) == abs(EXPA1_SF[1])) 	/* 'A' appears only as A^e and A^(-e). */
			{
			if(abs(EXPA1_SF[0]) > 1)	/* If |e| > 1. */
				{
				if(NumRelators == 1)	/* If there is only 1 relator R, R is disjoint from a proper-power A^(|e|). */
					{
					if(!Print) return(1);
					printf("\n\nR = %s is disjoint from a proper-power A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
					if(B10B11Recognized || Batch == 56) fprintf(H_Results," R = %s is disjoint from a proper-power A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
					return(1);
					}
				if(NumRelators == 2)	/* R is not disjoint from a proper-power. */
					{
					/* Ci is disjoint from a proper-power R' = A^(|e|), which must intersect R. */
					/* Compute |R.R'|. |R.R'| is equal to the number of appearances of 'A' in R with exponents A^f, |f| > 0, |f| ≠ |e|. */					
					Get_Genus_2_EXPS();
					for(i = 0,NumIntersections = 0; NEXA2_SF[i] && i < 8; i++)
						if(abs(EXPA2_SF[i]) != abs(EXPA1_SF[0])) NumIntersections += NEXA2_SF[i];
					if(NumIntersections > 1)
						{
						if(!Print) return(1);
						printf("\n\nC = %s is disjoint from a proper-power R' = A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
						printf("\nThen R = %s and R' lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
						printf("\nHence H[R] contains an essential torus bounding SFD(%d,%u).",NumIntersections,abs(EXPA1_SF[0]));
						if(B10B11Recognized || Batch == 56) 
							{
							fprintf(H_Results," C = %s is disjoint from a proper-power R' = A^%d.",(char *) *Relators[1],abs(EXPA1_SF[0]));
							fprintf(H_Results,"\nThen R = %s and R' lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
							fprintf(H_Results,"\nHence H[R] contains an essential torus bounding SFD(%d,%u).",NumIntersections,abs(EXPA1_SF[0]));
							}
						return(1);
						}
					}
				}
			else
				{
				/* 'A' appears only with exponents 1 and -1. */
				if((NEXA1_SF[0] == NEXA1_SF[1]) && (NEXA1_SF[0] == 1 || CheckForAltExpSigns(1,'A') == 1))
					{
					if(NEXB1_SF[2] == 0 && abs(EXPB1_SF[0]) == 1 && abs(EXPB1_SF[1]) <= 1)
						{
						/* 'B' also appears only with exponents ±1. */
						if(NumRelators == 1)
							{
							if(!Print) return(1);
							printf("\n\nGen 'A' appears in R = %s only with alternating ±1 exponents.",(char *) *Relators[1]);
							printf("\nThen R is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'B'.");
							printf("\nSo H[R] contains an essential non-separating annulus.");
							if(B10B11Recognized || Batch == 56) 
								{
								fprintf(H_Results," Gen 'A' appears in R = %s only with alternating +1,-1 exponents.",(char *) *Relators[1]);
								fprintf(H_Results,"\nThen R is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'B'.");
								fprintf(H_Results,"\nSo H[R] contains an essential non-separating annulus.");
								}						
							return(1);
							}
						if(NumRelators == 2)
							{
							/* Compute |R.R'|. |R.R'| is |m| when R abelianized is [R] = m[A] + n[B]. */
							Get_Genus_2_EXPS();
							for(i = 0,NumIntersections = 0; NEXA2_SF[i] && i < 8; i++) 
								NumIntersections += NEXA2_SF[i]*EXPA2_SF[i];	
							NumIntersections = abs(NumIntersections);
							if(NumIntersections > 1)
								{
								if(!Print) return(1);					
								printf("\n\nGen 'A' appears in C = %s only with alternating ±1 exponents.",(char *) *Relators[1]);
								printf("\nSo C is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'B'.");
								printf("\nThen R = %s and R' = B = bdry comp A1 lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
								printf("\nSo H[R] contains an essential separating annulus A2 cutting off a solid torus W with meridian m ");
								printf("such that |m.Bdry(A2)| = %d.",NumIntersections);
								if(B10B11Recognized || Batch == 56)
									{
									fprintf(H_Results," Gen 'A' appears in C = %s only with alternating +1,-1 exponents.",(char *) *Relators[1]);
									fprintf(H_Results,"\nSo C is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'B'.");
									fprintf(H_Results,"\nThen R = %s and R' = B = bdry comp A1 lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
									fprintf(H_Results,"\nSo H[R] contains an essential separating annulus A2 cutting off a solid torus W with meridian m ");
									fprintf(H_Results,"such that |m.Bdry(A2)| = %d.",NumIntersections);
									}							
								return(1);
								}
							}
						}	
					}
				}
			}
		}
		
	if(NEXB1_SF[2] == 0)	/* 'B' appears with at most 2 exponents. */
		{
		if(NEXB1_SF[1] == 0 && (abs(EXPB1_SF[0]) > 1))	/* 'B' appears only as B^e, e > 1. */
			{
			if(!Print) return(1);
			printf("\n\nR = %s is disjoint from a proper-power B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
			if(B10B11Recognized || Batch == 56) fprintf(H_Results," R = %s is disjoint from a proper-power B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
			return(1);
			}
		if(abs(EXPB1_SF[0]) == abs(EXPB1_SF[1]))	/* 'B' appears only as B^e and B^(-e). */
			{
			if(abs(EXPB1_SF[0]) > 1)	/* If |e| > 1. */
				{
				if(NumRelators == 1)	/* If there is only 1 relator R, R is disjoint from a proper-power B^(|e|). */
					{
					if(!Print) return(1);
					printf("\n\nR = %s is disjoint from a proper-power B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
					if(B10B11Recognized || Batch == 56) fprintf(H_Results," R = %s is disjoint from a proper-power B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
					return(1);
					}
				if(NumRelators == 2)	/* R is not disjoint from a proper-power. */
					{
					/* Ci is disjoint from a proper-power R' = B^(|e|), which must intersect R. */	
					/* Compute |R.R'|. |R.R'| is equal to the number of appearances of 'B' in R with exponents B^f, |f| > 0, |f| ≠ |e|. */
					Get_Genus_2_EXPS();
					for(i = 0,NumIntersections = 0; NEXB2_SF[i] && i < 8; i++)
						if(abs(EXPB2_SF[i]) != abs(EXPB1_SF[0])) NumIntersections += NEXB2_SF[i];
					if(NumIntersections > 1)
						{
						if(!Print) return(1);
						printf("\n\nC = %s is disjoint from a proper-power R' = B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
						printf("\nR = %s and R' lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
						printf("\nHence H[R] contains an essential torus bounding SFD(%d,%u).",NumIntersections,abs(EXPB1_SF[0]));
						if(B10B11Recognized || Batch == 56)
							{
							fprintf(H_Results," C = %s is disjoint from a proper-power R' = B^%d.",(char *) *Relators[1],abs(EXPB1_SF[0]));
							fprintf(H_Results,"\nR = %s and R' lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
							fprintf(H_Results,"\nHence H[R] contains an essential torus bounding SFD(%d,%u).",NumIntersections,abs(EXPB1_SF[0]));
							}
						return(1);
						}		
					}
				}
			else
				{
				/* 'B' appears only with exponents 1 and -1. */
				if((NEXB1_SF[0] == NEXB1_SF[1]) && (NEXB1_SF[0] == 1 || CheckForAltExpSigns(1,'B') == 1))
					{
					if(NEXA1_SF[2] == 0 && abs(EXPA1_SF[0]) == 1 && abs(EXPA1_SF[1]) <= 1)
						{
						/* 'A' also appears only with exponents ±1. */
						if(NumRelators == 1)
							{
							if(!Print) return(1);
							printf("\n\nGen 'B' appears in R = %s only with alternating ±1 exponents.",(char *) *Relators[1]);
							printf("\nThen R is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'A'.");
							printf("\nSo H[R] contains an essential non-separating annulus.");
							if(B10B11Recognized || Batch == 56)
								{
								fprintf(H_Results," Gen 'B' appears in R = %s only with alternating +1,-1 exponents.",(char *) *Relators[1]);
								fprintf(H_Results,"\nThen R is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'A'.");
								fprintf(H_Results,"\nSo H[R] contains an essential non-separating annulus.");
								}
							return(1);
							}
						if(NumRelators == 2)
							{
							/* Compute |R.R'|. |R.R'| is |n| when R abelianized is [R] = m[A] + n[B]. */
							Get_Genus_2_EXPS();
							for(i = 0,NumIntersections = 0; NEXB2_SF[i] && i < 8; i++) 
								NumIntersections += NEXB2_SF[i]*EXPB2_SF[i];	
							NumIntersections = abs(NumIntersections);
							if(NumIntersections > 1)
								{
								if(!Print) return(1);				
								printf("\n\nGen 'B' appears in C = %s only with alternating ±1 exponents.",(char *) *Relators[1]);
								printf("\nSo C is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'A'.");
								printf("\nThen R = %s and R' = A = bdry comp A1 lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
								printf("\nSo H[R] contains an essential separating annulus A2 cutting off a solid torus W with meridian m ");
								printf("such that |m.Bdry(A2)| = %d.",NumIntersections);
								if(B10B11Recognized || Batch == 56)
									{
									fprintf(H_Results," Gen 'B' appears in C = %s only with alternating +1,-1 exponents.",(char *) *Relators[1]);
									fprintf(H_Results,"\nSo C is disjoint from a non-separating annulus A1 in H with each bdry comp of A1 = 'A'.");
									fprintf(H_Results,"\nThen R = %s and R' = A = bdry comp A1 lie in an OPT F in Bdry H with Bdry F = C and |R.R'| = %d.",(char *) *Relators[2],NumIntersections);
									fprintf(H_Results,"\nSo H[R] contains an essential separating annulus A2 cutting off a solid torus W with meridian m ");
									fprintf(H_Results,"such that |m.Bdry(A2)| = %d.",NumIntersections);
									}								
								return(1);
								}					
							}
						}	
					}
				}
			}
		}

return(0);
}

int Genus_Two_One_Relator_Annuli_And_Tori_S2(unsigned int ZZ0,unsigned int ZZ1, unsigned int ZZ2, 
	unsigned int ZZ3, unsigned int Source, unsigned int NumReps,char F1,char Print)
{
	ZZ[0] = ZZ0;
	ZZ[1] = ZZ1;
	ZZ[2] = ZZ2;
	ZZ[3] = ZZ3;
	if(NumReps < 3)
		Do_Aut(Source,NumReps,NumRelators);
	else
		if(Do_Auts(Source,NumReps,NumRelators) == TOO_LONG) return(3);
		
	if(Micro_Print == 1)
		{						
		Micro_Print_Do_Aut(Source,NumReps);

		if(F1)
			{
			if(NumRelators == 2)
				{
				printf("\n\n%d) C = %s",F1,(char *) *Relators[1]);
				printf("\n   R = %s",(char *) *Relators[2]);
				}
			else
				printf("\n\n%d) R = %s",F1,(char *) *Relators[1]);
			}	
		if(!F1)
			{
			if(NumRelators == 2)
				{
				printf("\n\nC = %s",(char *) *Relators[1]);
				printf("\n    R = %s",(char *) *Relators[2]);
				}
			else	
				printf("\n\nR = %s",(char *) *Relators[1]);
			}
		}
	
	if(Genus_Two_One_Relator_Annuli_And_Tori_S1(Print)) return(1);
	
	return(0);
}	

int Get_Genus_Two_Commutators(char Flag1,char Print)
{
	/**********************************************************************************************
			Given a realizable non-separating simple closed curve R in Relators[1], 
		Get_Genus_Two_Commutators() finds the separating simple closed curves disjoint 
		from R, which are candidates for curves disjoint from proper-powers intersecting R 
		more than once. There are at most four such candidates. (Note this routine expects 
		the set of Dual_Relators[] to correspond to Relators[1].)
	**********************************************************************************************/							
							
	unsigned char 	NumCommutators,
					*p,
					*q,
					*r,
					**Temp;
	
	int				GTORRV,
					LTRV,
					WGRV;				
							
	unsigned int 	d,
					e,
					edgeLE,
					edgeRE,
					HS,
					i,
					j,
					length,
					ss,
					v,
					vertex,
					vertex1,
					w;

if(Flag1) goto _ALREADY_HAVE_DIAGRAM;

	/********************************************************************************************
						First try to find a realizable diagram of Relators[1].
	********************************************************************************************/

_GET_DIAGRAM:
    
    Saved_Vertices = 0;
    TestRealizability1 = TRUE;
    Vertices = 4;
    Fill_A(NumRelators);
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
    
    if(Sep_Surface() > 1) return(0);	/* H[R] has two boundary components. Don't need commutators.*/

_ALREADY_HAVE_DIAGRAM:

	HS = GetHandleSize((char **) Relators[1]);
	if(Temp1 != NULL) DisposeHandle((char **) Temp1);
	Temp1 = (unsigned char **) NewHandle(sizeof(char)*HS);	
	if(Temp1 == NULL) Mem_Error();
				
	for(vertex = NumCommutators = 0; vertex <= 2; vertex += 2)
		{
		for(ss = 0, vertex1 = FV[vertex]; ; )
			{
			ss += A[vertex][vertex1];
			if(ss > V[vertex]) break;
			edgeRE = ss;
			edgeLE = ss - 1;
			if(edgeRE == V[vertex]) edgeRE = 0;
			p = r = *DualRelators[(vertex >> 1) + 1] + edgeLE;
			r++;
			if(*r == EOS) r = *DualRelators[(vertex >> 1) + 1];
			if(abs(*p-*r) == 32)
				{
				vertex1 = CO[vertex][vertex1];
				continue;
				} 
			vertex1 = CO[vertex][vertex1];
			NumCommutators ++;

			if(Temp2 != NULL) DisposeHandle((char **) Temp2);
			Temp2 = (unsigned char **) NewHandle(2*HS);		
			if(Temp2 == NULL) Mem_Error();
	
			/******************************************************************************************
				Start at edgeLE of vertex vertex and record the word formed by this path, in the 
				string *Temp1, until we again arrive at edge edgeLE of vertex vertex.
			******************************************************************************************/	
	
			v = vertex;
			e = edgeLE;
			r = *Temp1;
			length = 0;		
			do
				{
				if(v & 1)
					{
					*r = (v >> 1) + 'a';
					w = v - 1;
					}
				else
					{
					*r = (v >> 1) + 'A';
					w = v + 1;
					}
				e = OSA[v] - e;
				if(e >= V[v]) e -= V[v];
				r++;
				if(++length >= HS) return(2); /* Error ! */
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					v = CO[w][v];
					d += A[w][v];
					}
				e = B[w][v] - e;
				}
			while(v != vertex || e != edgeLE);	
			*r = EOS;
		
			/******************************************************************************************
				Next, start at edgeRE of vertex vertex and record the word formed by this path, in 
				the string *Temp2, until we again arrive at edge edgeRE of vertex vertex.
			******************************************************************************************/	

			v = vertex;
			e = edgeRE;
			r = *Temp2;	
			length = 0;
			do
				{
				if(v & 1)
					{
					*r = (v >> 1) + 'a';
					w = v - 1;
					}
				else
					{
					*r = (v >> 1) + 'A';
					w = v + 1;
					}
				e = OSA[v] - e;
				if(e >= V[v]) e -= V[v];
				r++;
				if(++length >= HS) return(2); /* Error ! */
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					v = CO[w][v];
					d += A[w][v];
					}
				e = B[w][v] - e;
				}
			while(v != vertex || e != edgeRE);	
			*r = EOS;
						
			/***********************************************************
					Invert *Temp2 and concatenate *Temp1 and *Temp2.
			************************************************************/
					
			Inverse_Nr(*Temp2);  		
			p = *Temp1;
			while( (*r++ = *p++) ) ;			
			Freely_Reduce_Nr();		
			i = NumCommutators + 3;
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Temp2));	
			if(Relators[i] == NULL) Mem_Error();
			p = *Temp2;
			r = *Relators[i];
			while( (*r++ = *p++) ) ;								
			}
		}
	
	if(Micro_Print == 1 && Flag1) 
		{
		printf("\n\nHere are the %d separating curves C[i] disjoint from the input relator:\n",NumCommutators);
		for(i = 1; i <= NumCommutators; i++)
		printf("\nC[%d] = %s",i,(char *) *Relators[i+3]);
		printf("\n");
		}
	if(Flag1) return(NumCommutators);
	if(NumCommutators == 0) return(0);
			
	/****************************************************************************************** 
		For 1 <= i <= NumCommutators, check each (R,Ci) pair looking for a simple closed 
		curve R', disjoint from Ci, such that either R' is a proper-power intersecting R 
		more than once, or Ci is disjoint from a non-separating annulus whose bdry 
		components are primitives, one of which is R', and R' intersects R more than once. 
			First, stash a copy of Relators[1] in Relators[9].
	*******************************************************************************************/
	
	if(Relators[9] != NULL) DisposeHandle((char **) Relators[9]);
	Relators[9] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[1]));	
	if(Relators[9] == NULL) Mem_Error();
	p = *Relators[9];
	q = *Relators[1];
	while( (*p++ = *q++) ) ;
	
	NumRelators = 2;
	for(i = 1; i <= NumCommutators; i++)
		{
		Temp = Relators[1];
		Relators[1] = Relators[i + 3];
		Relators[i + 3] = Temp;
		if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
		Relators[2] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[9]));	
		if(Relators[2] == NULL) Mem_Error();
		p = *Relators[2];
		q = *Relators[9];
		while( (*p++ = *q++) ) ;
		Length = GetHandleSize((char **) Relators[1]) - 1;
		
		/************************************************************* 
			Reduce Ci to minimal length carrying R along. Then call 
			Genus_Two_One_Relator_Annuli_And_Tori(FALSE) and check if 
			Ci is disjoint from an R', as above.
		**************************************************************/
			
		if(Find_Flow_A(NORMAL,1) == TOO_LONG) return(2);
		
		if(Micro_Print == 1)
			{
			printf("\n\nC = %s",(char *) *Relators[1]);
			printf("\nR = %s \n",(char *) *Relators[2]);
			}
		
		GTORRV = Genus_Two_One_Relator_Annuli_And_Tori(FALSE,Print);
		if(GTORRV) return(GTORRV);	
		}
							
	return(0);
}

int	FindMinExpAndContext(char WhichGen, unsigned int MinExp)
{
	unsigned char	*p,
					*q,
					*r,
					sex,
					x,
					y,
					z;
					
	unsigned int	e,
					se;				
					
	/***************************************************************************************************
		If say, WhichGen = 'A', this routine returns 1, 2, 3 or 4 if it finds a subword of Relators[1]
		of the form 1, 2, 3, or 4 below with e = MinExp. Otherwise the routine returns 0.
			1) AB^eA
			2) Ab^eA
			3) aB^ea
			4) ab^ea	
	****************************************************************************************************/				
	
	r = *Relators[1];
			
	if(WhichGen == 'A')
		{
		for(p = r; (x = *p); p++) if((x == 'A' || x == 'a'))
			{
			y = x;
			sex = x;
			se = p - r;
			q = p;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'A' || x == 'a')) 
			{
			if(x == y) 
				{
				e = p - q - 1;
				if(e == MinExp)
					{
					z = *(q + 1);
					if(y == 'A' && z == 'B') return(1);
					if(y == 'A' && z == 'b') return(2);
					if(y == 'a' && z == 'B') return(3);
					if(y == 'a' && z == 'b') return(4);
					}
				}
			y = x;
			q = p;
			}
		if(x == EOS && y == sex)
			{
			e = se + p - q - 1;
			if(e == MinExp)
				{
				if(se) z = *r;
				else z = *(q + 1);
				if(y == 'A' && z == 'B') return(1);
				if(y == 'A' && z == 'b') return(2);
				if(y == 'a' && z == 'B') return(3);
				if(y == 'a' && z == 'b') return(4);
				}
			}
		}
		
	if(WhichGen == 'B')
		{
		for(p = r; (x = *p); p++) if((x == 'B' || x == 'b'))
			{
			y = x;
			sex = x;
			se = p - r;
			q = p;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'B' || x == 'b')) 
			{
			if(x == y) 
				{
				e = p - q - 1;
				if(e == MinExp)
					{
					z = *(q + 1);
					if(y == 'B' && z == 'A') return(1);
					if(y == 'B' && z == 'a') return(2);
					if(y == 'b' && z == 'A') return(3);
					if(y == 'b' && z == 'a') return(4);
					}
				}
			y = x;
			q = p;
			}
		if(x == EOS && y == sex)
			{
			e = se + p - q - 1;
			if(e == MinExp)
				{
				if(se) z = *r;
				else z = *(q + 1);
				if(y == 'B' && z == 'A') return(1);
				if(y == 'B' && z == 'a') return(2);
				if(y == 'b' && z == 'A') return(3);
				if(y == 'b' && z == 'a') return(4);
				}
			}
		}
		
	return(0);	
}

int Check_R1_Positivity(void)
{
	char			Slide;
	
	unsigned char	*p,
					*q,
					x,
					y;
	
	int				MinExp;
					
	unsigned int	AA,
					aa,
					BB,
					bb,
					AB,
					ba,
					Ab,
					Ba,
					BA,
					ab,
					aB,
					bA;
	
	/*********************************************************************************
		This routine determines if there exists a set of meridional disks for the 
		handlebody H of genus two in which Relators[1] is a positive non-separating
		cyclic word. Relevant because if no such set of disks exists, H[R] has at 
		most one cyclic, or reducing filling. It returns 0 if Relators[1] is 
		non-positive, returns 1 if Relators[1] is positive, and otherwise returns 2.
	**********************************************************************************/
			
	if(NumRelators != 1 || NumGenerators != 2) return(2);				
	
	while(1)
		{
		AA = aa = BB = bb = AB = ba = Ab = Ba = BA = ab = aB = bA = 0;					
		p = *Relators[1];
		if(*p == EOS) return(2);
		q = p;
		q++;
		x = *p;
		y = *q;
		if(y == EOS)
			{
			q = p;
			y = *q;
			}
		while(1)
			{
			switch(x)
				{
				case 'A':
					switch(y)
						{
						case 'A':
							AA++;
							break;
						case 'B':
							AB++;
							break;
						case 'b':
							Ab++;
							break;
						default: return(2);	
						}
					break;
				case 'a':
					switch(y)
						{
						case 'a':
							aa++;
							break;
						case 'B':
							aB++;
							break;
						case 'b':
							ab++;
							break;
						default: return(2);	
						}			
					break;
				case 'B':
					switch(y)
						{
						case 'A':
							BA++;
							break;
						case 'a':
							Ba++;
							break;
						case 'B':
							BB++;
							break;
						default: return(2);	
						}			
					break;
				case 'b':
					switch(y)
						{
						case 'A':
							bA++;
							break;
						case 'a':
							ba++;
							break;
						case 'b':
							bb++;
							break;
						default: return(2);	
						}			
					break;
				default: return(2);			
				}	
			if(q == p) break;
			x = y;
			q++;
			y = *q;		
			if(y == EOS) 
				{
				q = p;
				y = *q;
				}
			}
		
		if((AA + BA + bA) == 0) return(1); /* A does not appear in R1. */
		if((aa + ba + Ba) == 0) return(1); /* a does not appear in R1. */
		if((BB + AB + aB) == 0) return(1); /* B does not appear in R1. */
		if((bb + Ab + ab) == 0) return(1); /* b does not appear in R1. */
	
		/* Check for symmetry. (Necessary as Relator[1]'s realizability may not have been checked.) */
	
		if(AB != BA) return(2);
		if(ab != ba) return(2);
		if(aB != Ba) return(2);
		if(bA != Ab) return(2);
	
		if(AA && aa && BB && bb) return(0);
		if(AB && ba && Ab && Ba) return(0);
	
		if((AB + ba) == 0) return(1);
		if((Ab + Ba) == 0) return(1);
	
		if(!AB && !Ab) return(1); /* A does not appear in R1. */
		if(!AB && !Ba) return(1); /* B does not appear in R1. */
		if(!ba && !Ab) return(1); /* b does not appear in R1. */
		if(!ba && !Ba) return(1); /* a does not appear in R1. */
	
		if((aa + Ba + BB + aB) == 0) return(1); /* Bandsum of a and B along AB is positive. */
		if((AA + bb + Ab + bA) == 0) return(1); /* Bandsum of a and B along AB is positive. */
		if((aa + bb + ba + ab) == 0) return(1); /* Bandsum of a and b along Ab is positive. */
		if((AA + BB + AB + BA) == 0) return(1); /* Bandsum of a and b along Ab is positive. */
	
		/************************************************************************************************** 
		 If execution gets to this point, either (AB > 0 and ba > 0) or (Ab > 0 and Ba > 0), but not both. 
		**************************************************************************************************/
		
		if(AB && ba)
			{
			if(((AA + bA) && (aa + aB)) && ((Ab + bb) && (Ba + BB))) 
			
			/************************************************************************************************* 
								if(((AA + bA) && (aa + aB)) && ((Ab + bb) && (Ba + BB)))
				Then any outermost subdisk of a meridional disk of H based at vertex A and separating vertex b 
				from vertex a and vertex B, has essential intersections with edges of R1 in both Ab + bb and 
				Ba + BB. Hence has both positive and negative intersections with R1. Similarly, any other 
				outermost subdisks of meridional disks of H have both positive and negative intersections 
				with R1. So R1 is non-positive.
			**************************************************************************************************/
			
			return(0);
			
			/*************************************************************************************************
				If execution is here, then either (!AA && !bA) or (!aa && !aB) or (!Ab && !bb) or 
				(!Ba && !BB). Let W(R1) = AB + ba. Then there is an automorphism which replaces R1 with R1' 
				such that either R1' is clearly positive, or clearly non-positive, or W(R1') < W(R1).
				Since all W's are > 0, the routine eventually terminates with a decision that R1 is 
				positive, or R1 is non-positive.
			*************************************************************************************************/
			
			Slide = FALSE;
			if(!AA && !bA) Slide = 1;
			if(!Slide && !aa && !aB) Slide = 2;
			if(!Slide && !Ab && !bb) Slide = 3;
			if(!Slide && !Ba && !BB) Slide = 4;
			switch(Slide)
				{
				case 1:		/* Slide vertex A over vertex b. A --> Ab */
				case 2:
					MinExp = Pos_Relator_Check_Min_Exp('A','a','B','b');					
					Pos_Relator_Check_Do_Auts(1,0,0,1,2,MinExp);
					break;
				case 3:		/* Slide vertex b over vertex A. B --> Ba */
				case 4:
					MinExp = Pos_Relator_Check_Min_Exp('B','b','A','a');					
					Pos_Relator_Check_Do_Auts(0,1,1,0,0,MinExp);
					break;
				default:
					return(2);		
				}
			}
		if(Ab && Ba)
			{
			if(((AA + AB) && (aa + ba)) && ((BB + BA) && (ab + bb))) return(0);
			
			/**********************************************************************************
				In this case, let W(R1) = Ab + Ba. Note that W(R1) is well-defined since only 
				one of (AB > 0 and ba > 0) or (Ab > 0 and Ba > 0), but not both.
			***********************************************************************************/
			
			Slide = FALSE;			
			if(!AA && !AB) Slide = 1;
			if(!Slide && !aa && !ba) Slide = 2;
			if(!Slide && !BA && !BB) Slide = 3;
			if(!Slide && !ab && !bb) Slide = 4;
			switch(Slide)
				{
				case 1:		/* Slide vertex b over vertex a. B --> BA */
				case 2:
					MinExp = Pos_Relator_Check_Min_Exp('B','b','a','A');				
					Pos_Relator_Check_Do_Auts(0,1,0,1,0,MinExp);
					break;
				case 3:		/* Slide vertex a over vertex b. A --> AB */
				case 4:
					MinExp = Pos_Relator_Check_Min_Exp('A','a','b','B');					
					Pos_Relator_Check_Do_Auts(0,1,0,1,2,MinExp);
					break;
				default:
					return(2);		
				}		
			}
		}		
}

int Pos_Relator_Check_Do_Auts(unsigned int ZZ0,unsigned int ZZ1, unsigned int ZZ2, 
	unsigned int ZZ3, unsigned int Source, unsigned int NumReps)
{
	ZZ[0] = ZZ0;
	ZZ[1] = ZZ1;
	ZZ[2] = ZZ2;
	ZZ[3] = ZZ3;
	if(NumReps < 3)
		Do_Aut(Source,NumReps,NumRelators);
	else
		if(Do_Auts(Source,NumReps,NumRelators) == TOO_LONG) return(2);
	
	return(0);
}

int Pos_Relator_Check_Min_Exp(char Gen1,char Gen2,char Gen3,char Gen4)
{
	unsigned char	*p,
					*q,
					*r,
					sex,
					x,
					y,
					z;
					
	int				MinExp;
					
	unsigned int	e,
					se;				
					
	/***************************************************************************************************
		If Gen1 = 'X', then Gen2 = 'x', and Gen3 = 'Y', Gen4 = 'y'. This routine then looks for a
		subword of Relators[1] of the form XY^eX or xy^ex with e minimal, and sets MinExp equal to e.	
	****************************************************************************************************/				
	
	r = *Relators[1];
	
	MinExp = BIG_NUMBER;
			
	if(Gen1 == 'A')
		{
		for(p = r; (x = *p); p++) if((x == 'A' || x == 'a'))
			{
			y = x;
			sex = x;
			se = p - r;
			q = p;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'A' || x == 'a')) 
			{
			if(x == y) 
				{
				e = p - q - 1;
				if(e < MinExp)
					{
					z = *(q + 1);
					if(y == 'A' && z == Gen3) MinExp = e;
					if(y == 'a' && z == Gen4) MinExp = e;
					}
				}
			y = x;
			q = p;
			}
		if(x == EOS && y == sex)
			{
			e = se + p - q - 1;
			if(e > 0 && e < MinExp)
				{
				if(se) z = *r;
				else z = *(q + 1);
				if(y == 'A' && z == Gen3) MinExp = e;
				if(y == 'a' && z == Gen4) MinExp = e;				
				}
			}
		}
		
	if(Gen1 == 'B')
		{
		for(p = r; (x = *p); p++) if((x == 'B' || x == 'b'))
			{
			y = x;
			sex = x;
			se = p - r;
			q = p;
			break;
			}
		if(x == EOS) return(0);
		p++;
		for(; (x = *p); p++) if((x == 'B' || x == 'b')) 
			{
			if(x == y) 
				{
				e = p - q - 1;
				if(e < MinExp)
					{
					z = *(q + 1);
					if(y == 'B' && z == Gen3) MinExp = e;
					if(y == 'b' && z == Gen4) MinExp = e;
					}
				}
			y = x;
			q = p;
			}
		if(x == EOS && y == sex)
			{
			e = se + p - q - 1;
			if(e > 0 && e < MinExp)
				{
				if(se) z = *r;
				else z = *(q + 1);
				if(y == 'B' && z == Gen3) MinExp = e;
				if(y == 'b' && z == Gen4) MinExp = e;
				}				
			}
		}
				
	return(MinExp);	
}

int Init_Get_Universal_Minimizer_Waves(int NumHSReps,int* HSRepL)
{
	unsigned char	*p,
					*q;
				
	int				i,
					j,
					k,
					l,
					m,
					n,
					nn,
					UMWRV;
	
	for(i = n = nn = 0; i < NumHSReps; i++)
		{
		if(HSRepL[i] < 0) 
			{
			j = -HSRepL[i];
			k = 1;
			continue;
			}	
		if(HSRepL[i] >= INFINITE) 
			{
			l = HSRepL[i] - INFINITE;
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
			UMWRV = Get_Universal_Minimizer_Waves(3);	
			if(UMWRV >= 5)
				{
				if(UMWRV == 7) 
					{
					printf("\n\nHS %d P %d Dist >= 3 is the unique splitting of this manifold.",j,k);
					return(0);
					}
				if(++n == 1) printf("\n\nThe meridional disks of H in:");
				if(UMWRV == 5) printf(" HS %d P %d,",j,k);
				if(UMWRV == 6) 
					{
					nn ++;
					printf(" HS %d P %d Dist >= 3,",j,k);
					}
				if(UMWRV == 8) printf(" HS %d P %d Dist 2,",j,k);						
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
			
			for(m = 1; m <= NumRelators; m++)
				{
				if(Relators[m] != NULL) DisposeHandle((char **) Relators[m]);
				Relators[m] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][m]));
				if(Relators[m] == NULL) Mem_Error();
				p = *SUR[ReadPres][m];
				q = *Relators[m];
				while( (*q++ = *p++) ) ;
				}			
			
			UMWRV = Get_Universal_Minimizer_Waves(3);
			if(UMWRV >= 5)
				{
				if(UMWRV == 7) 
					{
					printf("\n\nHS %d P %d Dist >= 3 is the unique splitting of this manifold.",j,k);
					return(0);
					}
				if(++n == 1) printf("\n\nThe meridional disks of H in:");
				if(UMWRV == 5) printf(" HS %d P %d,",j,k);
				if(UMWRV == 6) 
					{
					nn ++;
					printf(" HS %d P %d Dist >= 3,",j,k);
					}
				if(UMWRV == 8) printf(" HS %d P %d Dist 2,",j,k);		
				}				
			k++;
			}
		if(j >= 10) break;	
		}
		
	if(n == 0) 
		{
		if(j == 1) printf("\nHeegaard checked 1 HS Rep and did not find Universal Minimizers.");
		else printf("\nHeegaard checked %d HS Reps and did not find Universal Minimizers.",j);
		}
	if(n == 1) printf(" are a set of Universal Minimizers.");
	if(n > 1)  printf(" are sets of Universal Minimizers.");
	if(nn) printf("\nIn addition, since there are splittings of distance >= 3, the manifold is hyperbolic.");
			
	return(0);	
}

int Get_Universal_Minimizer_Waves(char F1)
{
	/************************************************************************************************
			Given a minimal length genus two Heegaard diagram H[R1,R2] of a closed manifold
		M, this routine produces 2 or 4 test "waveguides", which Heegaard uses to try to determine 
		if the meridional disks of the underlying handlebody H are a set of "universal minimizers".
	************************************************************************************************/							

	char			c1,
					c2,
					c3,
					c4;
												
	unsigned char 	NumWaveGuides,
					*p,
					*q,
					*r,
					*s,					
					x,
					y;
	
	int				LFPPSFRV,
					UMWGS1RV,
					WGRV;
							
	unsigned int 	c,
					d,
					e,
					edgeLE,
					edgeRE,
					ee,
					HS,
					HSS,
					LT1,
					LT2,
					length,
					ss,
					v,
					vertex,
					w;

	/********************************************************************************************
			 First see if Relators[1] and Relators[2] have a suitable realizable diagram.
	********************************************************************************************/
    
    if(NumGenerators != 2 || NumRelators != 2) return(0);
    Vertices = 4;
    Saved_Vertices = 0;
    TestRealizability1 = TRUE;
    DrawingDiagrams = TRUE;
    Fill_A(NumRelators);
    WGRV = Whitehead_Graph();     
    switch(WGRV)
        {
        case NO_ERROR:
        	TestRealizability1 = FALSE;
        	DrawingDiagrams = FALSE;
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
        case SEP_PAIRS:
        default:
        	printf("\n\nThis routine requires a uniquely-realizable presentation. Heegaard did not find one. Sorry!");
        	if(Micro_Print == 1)
        		{
        		printf("\n\nDid not check the initial presentation for Universal Minimizers. Cause:");
        		Micro_Print_Whitehead_Graph_Return_Value(WGRV);
        		}
        	TestRealizability1 = FALSE;
        	DrawingDiagrams = FALSE;
            return(2);
        } 
    
    if(Sep_Surface() > 1) return(0);	/* H[R1,R2] is not closed.*/

    /*******************************************************************
    	Check if the bdry C of the separating disk of H separating the 
    	the two handles of H is freely reduced and "robust" in H'.
    *******************************************************************/	
       
	if(Get_Sep_Disk_Dual(TRUE))
		{
		Translate_2_Dual_Pres(*Temp2);
		if(F1 != 3) printf("\n\nThe curve C = %s separating the two handles of H was not freely reduced in H'. Can't find Universal-Minimizers!",*Temp2);
		return(0);		
		}
	if(Check_C_Robustness(FALSE,FALSE))
		{
		Translate_2_Dual_Pres(*Temp3);
		if(F1 != 3) printf("\n\nThe curve C = %s separating the two handles of H is not robust in H'. Can't find Universal-Minimizers!",*Temp3);
		return(0);
		}	
		    
	if(Micro_Print == 1)
		{
		printf("\n\nGens A and B appear in relators R1 and R2 with exponents having the following absolute values:");
    	printf("\nGen A exponents:"); 
    	for(c = 0; c < 3; c++) if(EXP[0][c] > 0) printf(" %u",EXP[0][c]);   
    	printf("\nGen B exponents:");
    	for(c = 0; c < 3; c++) if(EXP[1][c] > 0) printf(" %u",EXP[1][c]);
    	}
    	
    /******************************************************************************************
    	If a generator appears in the relators with exponents having only two absolute values,
    	which differ by one, or with exponents of absolute value one, this routine cannot 
    	verify the current meridional disks of the underlying handlebody H are a set of 
    	'universal minimizers'; So it returns a value ≠ 5. The routine returns 5 if it can 
    	verify the current set of meridional disks of H are a set of 'universal minimizers".
    	And returns 6 if, in addition, it has verified the Heegaard splitting is a distance 
    	>= 3 splitting.
    ******************************************************************************************/
    
    /******************************************************************************************
    									An example: 
    									
    				P = < A^12B^5A^12b^7, A^7b^12a^5b^12 > is realizable with:
    				 
      				WaveGuide1 = A^12b^7A^7, WaveGuide2 = B^7a^7B^12, 
      				WaveGuide3 = b^5a^5b^12, WaveGuide4 = A^12B^5A^5
    	
    	Although both 'A' and 'B' appear in individual WaveGuides only with one exponent,
    	the current meridional disks of H are a set of Universal Minimizers.
    	
    *******************************************************************************************/
    
    if(EXP[0][1] == 0 || EXP[1][1] == 0) 				return(0);
    if(EXP[0][0] == 0 && (EXP[0][2] - EXP[0][1] == 1)) 	return(0);
    if(EXP[1][0] == 0 && (EXP[1][2] - EXP[1][1] == 1)) 	return(0);
    if(EXP[0][0] == 1 || EXP[1][0] == 1) 				return(0);
  
    c1 = c2 = c3 = c4 = 'c';
    
	HSS = GetHandleSize((char **) Relators[1]);
	if(HSS < GetHandleSize((char **) Relators[2])) HSS = GetHandleSize((char **) Relators[2]);		
	if(Temp1 != NULL) DisposeHandle((char **) Temp1);
	Temp1 = (unsigned char **) NewHandle(HSS);	
	if(Temp1 == NULL) Mem_Error();
	if(Temp2 != NULL) DisposeHandle((char **) Temp2);
	Temp2 = (unsigned char **) NewHandle(HSS);		
	if(Temp2 == NULL) Mem_Error();
		    					
	for(ss = 1,NumWaveGuides = 0; ss <= 2*NumEdges && NumWaveGuides < 4; ss ++)
		{		
		/**************************************************************************************
			Determine which edges of the original diagram are connected by the edge ss of
			the dual diagram.
		**************************************************************************************/	
		
		for(v = c = 0; c + VWG[v] < ss; v++) c += VWG[v];
		w = ss - c;
		for(c = ee = 0,d = FV[v]; c < w; c++)
			{
			ee += A[v][d];
			d = CO[v][d];
			}
		e = ee - 1;
		if(v & 1)
			{	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			if(e) ee = e - 1;
			else ee = V[v] - 1;
			}
			
		/**************************************************************************************
					Check whether this edge has its ends on distinct relators. 
		**************************************************************************************/		
		
		if(v & 1)
			p = q = *DualRelators[(v >> 1) + 1] + ee;
		else
			p = q = *DualRelators[(v >> 1) + 1] + e;
		q++;
		if(! *q) q = *DualRelators[(v >> 1) + 1];
		
		x = *p,
		y = *q;
		if(x == y || abs(x - y) == 32) continue;
		if(x == c1 && y == c2) continue;
		if(x == c2 && y == c1) continue;
		if(x == c3 && y == c4) continue;
		if(x == c4 && y == c3) continue;
						
		vertex  = v;
		edgeRE 	= ee;
		edgeLE 	= e;
		edgeRE  = edgeRE % V[v];
		
			/*******************************************************************************
						Edges edgeRE and edgeLE are adjacent at vertex v and
						connect v to distinct vertices of the Heegaard diagram.
			*******************************************************************************/
		
		/******************************************************************************************
			Start at edge e of vertex v and record the word formed by this path, in the string
			*Temp1, until we arrive at edge edgeLE of vertex vertex.
		******************************************************************************************/	

		v = vertex;
		e = edgeLE;
		r = *Temp1;
		length = 0;		
		do
			{
			if(v & 1)
				{
				*r = (v >> 1) + 'a';
				w = v - 1;
				}
			else
				{
				*r = (v >> 1) + 'A';
				w = v + 1;
				}
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			r++;
			if(++length >= HSS) return(2);
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}
			e = B[w][v] - e;
			}
		while(v != vertex || e != edgeLE);	
		*r = EOS;
		LT1 = length;

		/******************************************************************************************
			Next, start at edge e of vertex v and record the word formed by this path, in the
			string *Temp2, until we arrive at edge edgeRE of vertex vertex.
		******************************************************************************************/	

		v = vertex;
		e = edgeRE;
		r = *Temp2;	
		length = 0;

		do
			{
			if(v & 1)
				{
				*r = (v >> 1) + 'a';
				w = v - 1;
				}
			else
				{
				*r = (v >> 1) + 'A';
				w = v + 1;
				}
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			r++;
			if(++length >= HSS) return(2); 
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}
			e = B[w][v] - e;
			}
		while(v != vertex || e != edgeRE);	
		*r = EOS;
		LT2 = length;
	
		/************************************************************
			Temp1 and Temp2 have a common initial segment which we
			strip off of both Temp1 and Temp2. Then the truncated
			Temp1 and Temp2 form a WaveGuide pair.
		*************************************************************/
		
		p = *Temp1;
		q = *Temp2;
		while(1)
			{
			if(*p == *q)
				{
				p++;
				q++;
				}
			else break;
			if(!*p && !*q) break;	
			}
					
		r = *Temp1;
		s = *Temp2;

		NumWaveGuides += 2;
		if(NumWaveGuides == 2) /* Set {c1,c2,c3,c4} so we won't return with WaveGuide1 and WaveGuide2 again. */
			{		
			c1 = x;
			c2 = y;
			if(c1 < 97) c3 = c1 + 32;
			else c3 = c1 - 32;
			if(c2 < 97) c4 = c2 + 32;
			else c4 = c2 - 32;
			}

		if(NumWaveGuides == 2)
			{
			HS = r + LT1 + 1 - p;
			if(Relators[3] != NULL) DisposeHandle((char **) Relators[3]);
			Relators[3] = (unsigned char **) NewHandle(HS);	
			if(Relators[3] == NULL) Mem_Error();
			r = *Relators[3];
			while( (*r++ = *p++) ) ;
			HS = s + LT2 + 1 - q;
			if(Relators[4] != NULL) DisposeHandle((char **) Relators[4]);
			Relators[4] = (unsigned char **) NewHandle(HS);	
			if(Relators[4] == NULL) Mem_Error();
			s = *Relators[4];
			while( (*s++ = *q++) ) ;
			if(Micro_Print == 1)
				{
				printf("\n\nR1 and R2 with common initial segments, and WaveGuides obtained by deleting common initial segments from R1 and R2:");
				printf("\nR1 = %s",(char *) *Temp1);
				printf("\nR2 = %s",(char *) *Temp2);		
				printf("\nWaveGuide1 = %s = ",(char *) *Relators[3]);
				ReWrite_WaveGuides(*Relators[3]);					
				printf("\nWaveGuide2 = %s = ",(char *) *Relators[4]);
				ReWrite_WaveGuides(*Relators[4]);
				}	
			}
			
		if(NumWaveGuides == 4)
			{
			HS = r + LT1 + 1 - p;
			if(Relators[5] != NULL) DisposeHandle((char **) Relators[5]);
			Relators[5] = (unsigned char **) NewHandle(HS);	
			if(Relators[5] == NULL) Mem_Error();
			r = *Relators[5];
			while( (*r++ = *p++) ) ;
			HS = s + LT2 + 1 - q;
			if(Relators[6] != NULL) DisposeHandle((char **) Relators[6]);
			Relators[6] = (unsigned char **) NewHandle(HS);	
			if(Relators[6] == NULL) Mem_Error();
			s = *Relators[6];
			while( (*s++ = *q++) ) ;
			if(Micro_Print == 1)
				{
				printf("\n\nR1 and R2 with common initial segments, and WaveGuides obtained by deleting common initial segments from R1 and R2:");
				printf("\nR1 = %s",(char *) *Temp1);
				printf("\nR2 = %s",(char *) *Temp2);			
				printf("\nWaveGuide3 = %s = ",(char *) *Relators[5]);
				ReWrite_WaveGuides(*Relators[5]);								
				printf("\nWaveGuide4 = %s = ",(char *) *Relators[6]);
				ReWrite_WaveGuides(*Relators[6]);
				}	
			}					
		}
	
	UMWGS1RV = NumWaveGuides;	
	if(NumWaveGuides) UMWGS1RV = Get_Universal_Minimizer_Waves_S1(NumWaveGuides);
	
	if(Micro_Print == 1) for(c = 1,c1 = '*'; c <= NumWaveGuides; c++)
		{
		if(c == 1) printf("\n");
		printf("\nWaveGuide%u A Exponents:",c);
		for(d = 2*c-2,e = 0;e < 3; e++) 
			{
			if(EXP[d][e]) printf(" %6u",EXP[d][e]);
			else printf(" %6c",c1);
			}
		printf("	WaveGuide%u B Exponents: ",c);
		for(d = 2*c-1,e = 0;e < 3; e++) 
			{
			if(EXP[d][e]) printf(" %6u",EXP[d][e]);
			else printf(" %6c",c1);
			}
		if(c == NumWaveGuides) printf("\n");
		}
   	
   	if(UMWGS1RV == 6 && F1 && (Look_For_PP_SF_Curves(NumWaveGuides,TRUE,F1) == 7)) return(7);
   	if(UMWGS1RV == 5 && F1) 
   		{
   		LFPPSFRV = Look_For_PP_SF_Curves(NumWaveGuides,FALSE,F1);
   		if(LFPPSFRV == 6) UMWGS1RV = 6;
   		if(LFPPSFRV == 8) UMWGS1RV = 8;
   		}
   											
	return(UMWGS1RV);
}

int Get_Universal_Minimizer_Waves_S1(unsigned char NumWaveGuides)
{
    /******************************************************************************************
    	If a generator appears in a WaveGuide with exponents having only two absolute values, 
    	which differ by one, or with exponents of absolute value one, Heegaard can not verify 
    	the current set of meridional disks of the underlying handlebody H are a set of 
    	"universal minimizing" disks; so this routine will return 1.
    ******************************************************************************************/   
    
    unsigned char  	i,
    				j,
    				k,
    				Nex,
                	*p,
                    x,
                    y;
                            
    unsigned int   	ex,
    				ex2,
                    *q; 
                    
    /************************************************************************************
		Stash copies of EXP[0][0],EXP[0][1],EXP[0][2],EXP[1][0],EXP[1][1],EXP[1][2],
		and NEX[0][0],NEX[0][1],NEX[0][2],NEX[1][0],NEX[1][1],NEX[1][2]. 
	************************************************************************************/
	
	for(i = 0; i < 2; i++) for(j = 0; j < 3; j++) 
		{
		EXP[i+9][j] = EXP[i][j];
		NEX[i+9][j] = NEX[i][j];
		}	                     
                    	
    for(j = 2 + NumWaveGuides; j > 2; j--)
        {
        for(i = 0; i < 2; i++) 
        for(x = 0; x < 3; x++) EXP[i][x] = 0;        
        p = *Relators[j];
        x = *p;
        if(x)
			{
			ex = 0;
			while( (y = *p++) )
				{
				if(x == y)
					ex++;
				else
					{
					if(x < 95) i = x - 65;
					else i = x - 97;
					for(x = 0,q = EXP[i]; x < 3 && ex != q[x] && q[x]; x++) ;
					if(x < 3) q[x] = ex;
					ex = 1;    
					}
				x = y;
				}
			if(y == EOS)
				{
				if(x < 95) i = x - 65;
				else i = x - 97;
				for(x = 0,q = EXP[i]; x < 3 && ex != q[x] && q[x]; x++) ;
				if(x < 3) q[x] = ex;    
				}
			}
		
 		k = 2*j - 6;
 		if(k > 0) for(i = 0; i < 3; i++) 
 			{
 			EXP[k][i] 	= EXP[0][i];
 			EXP[k+1][i] = EXP[1][i];
 			}
 		}
 
 		for(i = 0; i < 2*NumWaveGuides; i++)
 			{
 			if(EXP[i][0] == 0)					 					return(1);
 			if(EXP[i][0] > 0 && EXP[i][1] == 0 && EXP[i][0] < 5)    return(1);
 			if(EXP[i][2] == 0 && (abs(EXP[i][0] - EXP[i][1]) == 1)) return(1);
 			if(EXP[i][0] == 1 || EXP[i][1] == 1 || EXP[i][2] == 1)  return(1);
 			}
    	
    /****************************************************************************************** 	
    	Look for WaveGuides in which gen 'A' or gen 'B' appears only with one exponent, say 
    	ex, with ex >= 5 and that generator appears in the relators only with other exponents 
    	congruent to ±1 mod ex. If this occurs we return(1).
    *******************************************************************************************/
    
    for(i = 0,Nex = 0; i < 2*NumWaveGuides; i+= 2) if(EXP[i][0] > 0 && EXP[i][1] == 0)
    	{
    	ex = EXP[i][0];
    	Nex ++;
    	if(ex < 5) return(1);
		for(k = 0; k < 3; k++) if(EXP[9][k] > 0)
			{
			if(EXP[9][k] == ex) continue;
			ex2 = EXP[9][k];
			if(((ex2 + 1) % ex) == 0) return(1);
			if(((ex2 - 1) % ex) == 0) return(1);
			break;
			}
    	}
    	
    for(i = 1; i < 2*NumWaveGuides; i+= 2) if(EXP[i][0] > 0 && EXP[i][1] == 0)
    	{
    	ex = EXP[i][0];
    	Nex ++;
    	if(ex < 5) return(1);
		for(k = 0; k < 3; k++) if(EXP[10][k] > 0)
			{
			if(EXP[10][k] == ex) continue;
			ex2 = EXP[10][k];
			if(((ex2 + 1) % ex) == 0) return(1);
			if(((ex2 - 1) % ex) == 0) return(1);
			break;
			}
    	}	 
	    
    if(Nex == 0) return(6);
    return(5);       
}                                

int Get_Sep_Disk_Dual(char Flag1)
{	
	unsigned char	*p,
					*q,
					**Temp;

	unsigned int	HS,
					m,
					n;
	
	if(A[0][1] == 0) return(0);
		
	HS = GetHandleSize((char **) DualRelators[1]);
	if(Temp2 != NULL) DisposeHandle((char **) Temp2);
	Temp2 = (unsigned char **) NewHandle(2*HS);		
	if(Temp2 == NULL) Mem_Error();
	
	n = OSA[0] - B[0][1];
	if(n >= V[0]) n -= V[0];	
	p = *DualRelators[1];
	p+= n;
	q = *Temp2;
	while( (*q++ = *p++) ) ;
	
	q--;
	p = *DualRelators[1];
	for(m = 0; m < n; m++) *q++ = *p++;
	*q = EOS;
	
	Inverse_Nr(*Temp2);  		
	p = *DualRelators[1];
	while( (*q++ = *p++) ) ;			
	Freely_Reduce_Nr();			
	if(Flag1)
		{
		m = 2*(HS - A[0][1]) - 1;
		if(GetHandleSize((char **) Temp2) < m) return(1);	/* The bdry of the separating disk C is not freely reduced in H'. */	
		Temp = Temp2;
		Temp2 = Temp3;
		Temp3 = Temp;	
		return(0);
		}
	Translate_2_Dual_Pres(*Temp2);	
	printf("\n\nIn handlebody H', Sep_Disk_Dual C = %s",*Temp2);
	printf("\n(The Sep_Disk_Dual C, used with options 'c' and 'P', can help check distances of splittings when Universal Minimizers exist. E.g. ");
	printf("primitives and proper-powers in H', disjoint from C, are the only 'disjoint curves' of a distance 2 splitting.)");
	return(0);	
}

void ReWrite_WaveGuides(unsigned char* MyWaveGuide)
{
	unsigned char	*p,
					x,
					y;
	
	unsigned int	ex;
			
		p = MyWaveGuide;
		x = *p++;
		if(!x) return;			/* Relators[i] is empty!  */
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
		else return; 			/* Relators[i] is a proper power!  */
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

int P_and_PP_Curves_Disjoint_From_Relators(char Flag2)
{
	char			M1,
					M2,
					PorPP,
					str1[6],
					x;
	
	unsigned char 	Flag1,
					i,
					j,
					*p,
					*r,
					**Temp;
	
	int				GTCRV,
					LTRV,
					WGRV;
							
	unsigned int 	d,
					e,
					edgeLE,
					edgeRE,
					HS,
					length,
					NumCurves,
					ss,
					v,
					vertex,
					vertex1,
					w;
									
	/********************************************************************************************
						First try to find a realizable diagram.
	********************************************************************************************/

_GET_DIAGRAM:
    
    Saved_Vertices = 0;
    TestRealizability1 = TRUE;
    Vertices = 4;
    Fill_A(NumRelators);
    if(Flag2 && Find_Flow_A(NORMAL,FALSE)) return(2);   
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
            printf("\n\nThis routine requires R to have a uniquely-realizable Heegaard diagram. Heegaard did not find one. Sorry!");
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
                	printf("\n\nUnable to remove all separating pairs of vertices.");	
                    return(2);
                case 2: 
                	{
                	if(Micro_Print == 1)
                		printf("\n\nPerformed some level-transformations on the input presentation.");	   
                	goto _GET_DIAGRAM;
                	}
                default:
                	TestRealizability1 = FALSE;
                	printf("\n\nUnable to remove all separating pairs of vertices.");			
                    return(2);
                }    
        default:
        	TestRealizability1 = FALSE;
        	printf("\n\nThis routine requires R to have a uniquely-realizable Heegaard diagram. Heegaard did not find one. Sorry!");
            if(Micro_Print == 1)
            	{
            	printf("\n\nWhitehead_Graph() returned an error. Cause:");
            	Micro_Print_Whitehead_Graph_Return_Value(WGRV);
            	}        	
            return(2);
        }
    
    TestRealizability1 = FALSE; 

	if(Sep_Surface() <= 1 && Flag2) 
		{
		/************************************ 
			Relators[1] is non-separating. 
		************************************/
		
		if(NumRelators > 1) return(0);
		NumSaved = 0;
		
		/*******************************************
		 	Stash a copy of Relators[1] in Temp3. 
		********************************************/
		
		HS = GetHandleSize((char **) Relators[1]); 
		if(Temp3 != NULL) DisposeHandle((char **) Temp3);
		Temp3 = (unsigned char **) NewHandle(sizeof(char)*HS);	
		if(Temp3 == NULL) Mem_Error();
		p = *Relators[1];
		r = *Temp3;
		while( (*r++ = *p++) ) ;
		
		/*****************************************
			Check that Relators[1] is 'robust'.	
		******************************************/
		
		if(Check_C_Robustness(FALSE,FALSE))
			{
			printf("\n\nThe diagram of the non-separating input curve R is not 'robust'.");
			printf("\nHence can't locate curves disjoint from R which might also be disjoint from a disk in H.");
			return(2);
			}
		else if(Micro_Print == 1) printf("\n\nThe diagram of the non-separating input relator R is 'robust'.");		
		
		/************************************************************************************************ 	
			Get the distinguished slope representatives M1 and M2 and check if M1 or M2 is primitive 
			or a proper-power. If R is non-positive, the only simple closed curves, disjoint from R, 
			which might be primitives or proper-powers in H, are the two distinguished-slope 
			representatives M1 and M2. 
		*************************************************************************************************/	
		
		M1 = M2 = FALSE; 
		if(Genus_Two_Meridian_Reps(0,-1) == 0) for(j = 1; j <= 2; j++)
			{
			if(Temp4 != NULL) DisposeHandle((char **) Temp4);
			Temp4 = (unsigned char **) NewHandle(GetHandleSize((char**) Relators[j]));	
			if(Temp4 == NULL) Mem_Error();
			p = *Relators[j];
			r = *Temp4;
			while( (*r++ = *p++) ) ;
			if(Micro_Print == 1) printf("\n\nM%d = %s",j,*Temp4);
			Length = GetHandleSize((char **) Relators[j]) - 1;			
			SLength = Length;
			NumRelators = 1;
			if(j == 2)
				{
				Temp = Relators[1];
				Relators[1] = Relators[2];
				Relators[2] = Temp;
				}

			/****************************************************************** 
				Check if Relators[1] is already a primitive or proper-power. 
			******************************************************************/
				
			p = *Relators[1];
			x = *p;
			if(x) 
				{
				while( (x == *p)  ) p++;
				if(*p == EOS) 
					{
					Save_P_or_PP(Temp4,GetHandleSize((char**) Temp4));									
					if(j == 1) M1 = TRUE;
					if(j == 2) M2 = TRUE;
					}
				}	
										
			if(Find_Flow_A(NORMAL,FALSE) && Length < SLength) 
				{
				Save_P_or_PP(Temp4,GetHandleSize((char**) Temp4));				
				if(j == 1) M1 = TRUE;
				if(j == 2) M2 = TRUE;
				}		
			}			
					
		/******************************************************************************************** 
			Restore Relators[1] from Temp3 and check if R = Relators[1] is positive or non-positive. 
		*********************************************************************************************/
		
		HS = GetHandleSize((char **) Temp3); 
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(sizeof(char)*HS);	
		if(Relators[1] == NULL) Mem_Error();
		p = *Temp3;
		r = *Relators[1];
		while( (*r++ = *p++) ) ;
		NumRelators = 1;
		Fill_A(NumRelators);
       	i = Check_R1_Positivity();
       	
        if(i == 0)
        	{
			/****************************************************************************************************			
				The input relator R is non-positive, so the only possible primitives or proper-powers disjoint 
				from R are the 'distinguished-slope' representatives M1 and M2.
			****************************************************************************************************/
			
			if(NumSaved) 
				{			
				printf("\n\nHere are the primitives and proper-powers disjoint from the non-separating, non-positive input relator:\n");
				if(M1 && M2)
					{
					printf("\n1) M1 = %s",*Relators[14]);
					if(NumSaved > 1) printf("\n2) M2 = %s",*Relators[15]);
					}
				if(M1 && !M2) printf("\n1) M1 = %s",*Relators[14]);
				if(!M1 && M2) printf("\n1) M2 = %s",*Relators[14]);				
				}
			if(!NumSaved) printf("\n\nThere are no primitives or proper-powers disjoint from the non-separating, non-positive input relator.\n");	
			return(0);				       	
        	}
        if(i == 1) 
        	{
        	/*************************************************************************************************
        		Since R is positive, we locate the 4 commutators C1,C2,C3,C4 disjoint from R. Then the only
        		primitives or proper-powers disjoint from R are also disjoint from one of C1,C2,C3,C4.
        	**************************************************************************************************/
        	
        	HS = GetHandleSize((char **) Temp3); 
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			Relators[1] = (unsigned char **) NewHandle(sizeof(char)*HS);	
			if(Relators[1] == NULL) Mem_Error();
			p = *Temp3;
			r = *Relators[1];
			while( (*r++ = *p++) ) ;
			Fill_A(NumRelators);
			
			GTCRV = Get_Genus_Two_Commutators(TRUE,TRUE);
		
			if(GTCRV) NumRelators = 2;
			for(j = 1; j <= GTCRV; j++)
				{
				if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
				Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Temp3));	
				if(Relators[1] == NULL) Mem_Error();
				p = *Temp3;
				r = *Relators[1];
				while( (*r++ = *p++) ) ;
				if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
				Relators[2] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[j+3]));	
				if(Relators[2] == NULL) Mem_Error();
				p = *Relators[j+3];
				r = *Relators[2];
				while( (*r++ = *p++) ) ;
				Length =  GetHandleSize((char **) Relators[1]) - 1;
				Length += GetHandleSize((char **) Relators[2]) - 1;							
				P_and_PP_Curves_Disjoint_From_Relators(FALSE);
				}
			if(NumSaved) 
				{			
				printf("\n\nHere are the primitives and proper-powers disjoint from the non-separating, positive input relator:\n");
				if(M1 && M2)
					{
					printf("\n1) M1 = %s",*Relators[14]);
					if(NumSaved > 1) printf("\n2) M2 = %s",*Relators[15]);
					for(j = 3; j <= NumSaved; j++) printf("\n%d) R = %s",j,*Relators[13+j]);
					}
				if(M1 && !M2)
					{
					printf("\n1) M1 = %s",*Relators[14]);
					for(j = 2; j <= NumSaved; j++) printf("\n%d) R = %s",j,*Relators[13+j]);
					}
				if(!M1 && M2)
					{
					printf("\n1) M2 = %s",*Relators[14]);
					for(j = 2; j <= NumSaved; j++) printf("\n%d) R = %s",j,*Relators[13+j]);
					}
				if(!M1 && !M2) for(j = 1; j <= NumSaved; j++) printf("\n%d) R = %s",j,*Relators[13+j]);
				}
			if(!NumSaved) printf("\n\nThere are no primitives or proper-powers disjoint from the non-separating, positive input relator.\n");		
			return(0);	
        	}		
		}

	HS = GetHandleSize((char **) Relators[1]);
	if(NumRelators == 2 && GetHandleSize((char **) Relators[2]) > HS) HS = GetHandleSize((char **) Relators[2]);
	if(Temp1 != NULL) DisposeHandle((char **) Temp1);
	Temp1 = (unsigned char **) NewHandle(sizeof(char)*HS);	
	if(Temp1 == NULL) Mem_Error();
						
	for(vertex = NumCurves = 0,Flag1 = TRUE; vertex <= 2; vertex += 2)
		{
		for(ss = 0, vertex1 = FV[vertex]; ; )
			{
			ss += A[vertex][vertex1];
			if(ss > V[vertex]) break;
			edgeRE = ss;
			edgeLE = ss - 1;
			if(edgeRE == V[vertex]) edgeRE = 0;
			p = r = *DualRelators[(vertex >> 1) + 1] + edgeLE;
			r++;
			if(*r == EOS) r = *DualRelators[(vertex >> 1) + 1];
			if(abs(*p-*r) != 32)
				{
				vertex1 = CO[vertex][vertex1];
				continue;
				} 
				
			str1[NumCurves] = *p;

			if(Flag1)
				{
				/***********************************************************************************************
					When there is 1 relator, we need to verify that the diagram of the separating curve C
					is 'robust'.
					When there are 2 relators, say C and R', we need to verify that the subdiagram of the 
					separating curve C is 'robust'. In this case, this ensures this routine finds each curve 
					R, disjoint from C and R', such that R might also be disjoint from a disk in H.
					Note 'robust' means each 'outermost subdisk D of each disk of H has |D intersect C| >= 3. 				 
				************************************************************************************************/
				
				Flag1 = FALSE;
				v = vertex;
				e = edgeLE;
				r = *Temp1;
				length = 0;		
				do
					{
					if(v & 1)
						{
						*r = (v >> 1) + 'a';
						w = v - 1;
						}
					else
						{
						*r = (v >> 1) + 'A';
						w = v + 1;
						}
					e = OSA[v] - e;
					if(e >= V[v]) e -= V[v];
					r++;
					if(++length >= HS) return(2); /* Error ! */
					v = FV[w];
					d = A[w][v];
					while(d <= e)
						{
						v = CO[w][v];
						d += A[w][v];
						}
					e = B[w][v] - e;
					}
				while(v != vertex || e != edgeLE);	
				*r = EOS;
				
				if(Check_C_Robustness(Flag2,TRUE))
					{
					if(NumRelators == 1) 
						printf("\n\nThe diagram of the separating curve C is not 'robust'.");
					else
						printf("\n\nThe subdiagram of the separating curve C is not 'robust'.");
					printf("\nHence can't locate curves disjoint from C which might also be disjoint from a disk in H.");
					return(2);
					}
				else if(Micro_Print == 1) 
					{
					printf("\n\nThe current separating curve C is 'robust'. Here C = %s",*Temp1);
					printf("\nThe non-separating primitive, proper-power candidates disjoint from C are:\n");
					}			
				}
				
			/***********************************************************************************************
				Start at edge e = B[vertex][vertex1] - edgeLE of vertex vertex1 and record the word formed 
				by this path, in the string *Temp1, until we arrive at edge edgeRE of vertex vertex.
			***********************************************************************************************/	
		
			v = vertex1;
			e = B[vertex][vertex1] - edgeLE;
			if(e >= V[vertex1]) e -=V[vertex1];
			vertex1 = CO[vertex][vertex1];
			r = *Temp1;
			length = 0;		
			do
				{
				if(v & 1)
					{
					*r = (v >> 1) + 'a';
					w = v - 1;
					}
				else
					{
					*r = (v >> 1) + 'A';
					w = v + 1;
					}
				e = OSA[v] - e;
				if(e >= V[v]) e -= V[v];
				r++;
				if(++length >= HS) return(2); /* Error ! */
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					v = CO[w][v];
					d += A[w][v];
					}
				e = B[w][v] - e;
				}
			while(v != vertex || e != edgeRE);	
			*r = EOS;
			
			NumCurves ++;
			i = NumCurves + 7;			
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(length + 1);	
			if(Relators[i] == NULL) Mem_Error();
			p = *Temp1;
			r = *Relators[i];
			while( (*r++ = *p++) ) ;
			if(Micro_Print == 1) printf("\nC%d = %s",NumCurves,*Relators[i]);						
			}		
		}
		
	if(Flag2 == FALSE)
		{
		if(Micro_Print == 1) printf("\n\nChecking if any curve Ci, disjoint from R and separating curve C, is primitive or a proper-power:");
		for(i = 1; i <= NumCurves; i++)
			{		
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i+7]));	
			if(Relators[1] == NULL) Mem_Error();
			p = *Relators[i+7];
			r = *Relators[1];
			while( (*r++ = *p++) ) ;
		
			if(Temp4 != NULL) DisposeHandle((char **) Temp4);
			Temp4 = (unsigned char **) NewHandle(GetHandleSize((char**) Relators[1]));	
			if(Temp4 == NULL) Mem_Error();
			p = *Relators[1];
			r = *Temp4;
			while( (*r++ = *p++) ) ;
			
			if(Micro_Print == 1) printf("\n\nChecking curve C%d = %s",i,*Relators[1]); 
				
			Length = GetHandleSize((char**) Relators[1]) - 1;
			NumRelators = 1; 
		
			/****************************************************************** 
				Check if Relators[1] is already a primitive or proper-power. 
			******************************************************************/
			
			p = *Relators[1];
			x = *p;
			if(x) 
				{
				while( (x == *p)  ) p++;
				if(*p == EOS) 
					{
					Save_P_or_PP(Temp4,GetHandleSize((char**) Temp4));
					if(Micro_Print == 1) printf("\nC%d is primitive or a proper-power.",i);
					}
				}
			
			SLength = Length;		
			if(Find_Flow_A(NORMAL,FALSE) && Length < SLength) 
				{
				Save_P_or_PP(Temp4,GetHandleSize((char**) Temp4));
				if(Micro_Print == 1) printf("\nC%d is primitive or a proper-power.",i);
				}
		
			NumRelators = 2;
			}
		}	
	if(Flag2 == FALSE) return(0);		
	
	if(NumRelators == 1)
		{
		printf("\n\n(C is 'robust', so if H[C] embeds in S^3, one of the cusps of H[C] must be filled along a curve R below.");
		printf("\nIn addition, if M1 and M2 appear with R, then H[R] embeds in S^3 iff H[M1,M2] = S^3.)");
		}
		
	for(i = 1; i <= NumCurves; i++) 
		{
		printf("\n\n%u) Disjoint Nonseparating Curve %d, Side %c of C: R = %s",i,i,str1[i-1],(char *) *Relators[i+7]);
		
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i+7]));	
		if(Relators[1] == NULL) Mem_Error();
		p = *Relators[i+7];
		r = *Relators[1];
		while( (*r++ = *p++) ) ;
		Length = GetHandleSize((char**) Relators[1]) - 1;
		SLength = Length;
		
		/****************************************************************** 
			Check if Relators[1] is already a primitive or proper-power. 
		******************************************************************/
		
		PorPP = FALSE;
		p = *Relators[1];
		x = *p;
		if(x) 
			{
			while( (x == *p)  ) p++;
			if(*p == EOS)
				{
				if(Length == 1)
					printf("\n R is primitive. R = %s",(char *) *Relators[1]);
				else
					printf("\n R is a proper-power. R = %s",(char *) *Relators[1]);
				PorPP = TRUE;
				}
			}
		
		if(Find_Flow_A(NORMAL,FALSE))
			{
			if(Length < SLength)
				{
				if(Length == 1)
					printf("\n R is primitive. Automorphism(s) reduced R to: ");
				else
					printf("\n R is a proper-power. Automorphism(s) reduced R to: ");
				printf("%s",(char *) *Relators[1]);
				PorPP = TRUE;
				}
			}
		if(!PorPP) printf("\n R is not primitive or a proper-power.");	

		if(NumRelators == 1 && Genus_Two_Meridian_Reps(0,-2) == 0) 
			{
			printf("\nComputing H_1(H[M1,M2]): ");
			NumRelators = 2;			
			Compute_Homology(2);
			NumRelators = 1;
			}		
		}
		
	return(0);	
}

int Check_C_Robustness(char Flag1,char Flag2)
{	
	unsigned char	*p,
					*q,
					x,
					y;
						
	unsigned int	AA,
					aa,
					BB,
					bb,
					AB,
					ba,
					Ab,
					Ba,
					BA,
					ab,
					aB,
					bA;
	
	/*********************************************************************************
		This routine determines if the Whitehead graph of the Heegaard diagram of
		the relator in Temp1 or Temp3 is 'robust'.
	**********************************************************************************/
	
	AA = aa = BB = bb = AB = ba = Ab = Ba = BA = ab = aB = bA = 0;					
	if(Flag2) p = *Temp1;
	else p = *Temp3;	
	if(*p == EOS) return(2);
	q = p;
	q++;
	x = *p;
	y = *q;
	if(y == EOS)
		{
		q = p;
		y = *q;
		}
	while(1)
		{
		switch(x)
			{
			case 'A':
				switch(y)
					{
					case 'A':
						AA++;
						break;
					case 'B':
						AB++;
						break;
					case 'b':
						Ab++;
						break;
					default: return(2);	
					}
				break;
			case 'a':
				switch(y)
					{
					case 'a':
						aa++;
						break;
					case 'B':
						aB++;
						break;
					case 'b':
						ab++;
						break;
					default: return(2);	
					}			
				break;
			case 'B':
				switch(y)
					{
					case 'A':
						BA++;
						break;
					case 'a':
						Ba++;
						break;
					case 'B':
						BB++;
						break;
					default: return(2);	
					}			
				break;
			case 'b':
				switch(y)
					{
					case 'A':
						bA++;
						break;
					case 'a':
						ba++;
						break;
					case 'b':
						bb++;
						break;
					default: return(2);	
					}			
				break;
			default: return(2);			
			}	
		if(q == p) break;
		x = y;
		q++;
		y = *q;		
		if(y == EOS) 
			{
			q = p;
			y = *q;
			}
		}

if(Flag1) printf("\n\nInput Separating Curve: C = %s",(char *) *Temp1);
if(Flag2) 
	{	
	if((AA + aa + aB + bA) < 3) return(1);
	if((AA + aa + ab + BA) < 3) return(1);
	if((BB + bb + Ab + Ba) < 3) return(1);
	if((BB + bb + ab + BA) < 3) return(1);
	}
else
	{
	if((AA + aa + aB + bA) < 2) return(1);
	if((AA + aa + ab + BA) < 2) return(1);
	if((BB + bb + Ab + Ba) < 2) return(1);
	if((BB + bb + ab + BA) < 2) return(1);
	}	

/*
printf("\n\n AA %d, aa %d, BB %d, bb %d, AB %d, ba %d, Ab %d, Ba %d, BA %d, ab %d, aB %d, bA %d",AA , aa , BB , bb , AB , ba , Ab , Ba , BA , ab , aB , bA);
*/	
	
	return(0);
}

int Save_P_or_PP(unsigned char** Str1,unsigned int HS)
{
	unsigned char	*p,
					*q;
	
	int				i;
	
	if(NumSaved == 0)
		{
		if(Relators[14] != NULL) DisposeHandle((char **) Relators[14]);
		Relators[14] = (unsigned char **) NewHandle(sizeof(char)*HS);	
		if(Relators[14] == NULL) Mem_Error();
		p = *Str1;
		q = *Relators[14];
		while( (*q++ = *p++) ) ;
		NumSaved ++;
		return(0);
		}
	for(i = 1; i <= NumSaved; i++)
		if(GetHandleSize((char **) Relators[13+i]) == HS && Compare_Str(*Relators[13+i],*Str1,HS-1)) return(i);
	Inverse(*Str1);
	for(i = 1; i <= NumSaved; i++)
		if(GetHandleSize((char **) Relators[13+i]) == HS && Compare_Str(*Relators[13+i],*Str1,HS-1)) 
			{
			Inverse(*Str1);
			return(-i);
			}	
	Inverse(*Str1);	
	if(Relators[14+NumSaved] != NULL) DisposeHandle((char **) Relators[14+NumSaved]);
	Relators[14+NumSaved] = (unsigned char **) NewHandle(HS);	
	if(Relators[14+NumSaved] == NULL) Mem_Error();
	p = *Str1;
	q = *Relators[14+NumSaved];
	while( (*q++ = *p++) ) ;
	NumSaved ++;
	return(0);
}

int Look_For_PP_SF_Curves(unsigned char NumWaveGuides,char F1,char F2)
{
	char			FA,
					FB;
						
	unsigned char	NSL[13],
					*p,
					*q,
					*r,
					*W1 = NULL,
					*W2 = NULL,
					*W3 = NULL,
					*W4 = NULL,
					WGA[5],
					WGB[5];
					
	int				d,
					e,
					j,
					ss,
					vertex,
					vertex1,
					v,
					w;
				
	unsigned int 	Exp1,
					Exp2,
					Exp3,
					HS,
					length,
					MaxL,
					NExp1,
					NExp2,
					NExp3,
					NSEL[13],
					NumStowed;
						
	/************************************************************************************************* 	
	 	If F1, check if at least two of the exponents appearing in each WaveGuide are exponents 
	 	also appearing in one of relators R1 or R2. Else set FA or FB TRUE.
	*************************************************************************************************/
	
	FA = FB = FALSE;
	if(F1)
		{
		for(d = 1; d <= NumWaveGuides; d++) WGA[d] = WGB[d] = 0;
		for(d = 0; d < 3; d++) if(EXP[9][d] > 0)
			{
			Exp1 = EXP[9][d];
			for(e = 1; e <= NumWaveGuides; e++) 
			for(j = 0; j < 3; j++) if(EXP[2*e-2][j] == Exp1) WGA[e] ++;
			}
		for(d = 1; d <= NumWaveGuides; d++) if(WGA[d] < 1)
			{
			if(Micro_Print == 1) printf("\n\nWon't look for (PP,SF) curves! Gen 'A' does not appear with any exponents also appearing in R1 or R2.");
			return(2);
			}	
		for(d = 1; d <= NumWaveGuides; d++) if(WGA[d] == 1) 
			{
			FA = TRUE;
			break;
			}
		
		for(d = 0; d < 3; d++) if(EXP[10][d] > 0)
			{
			Exp1 = EXP[10][d];
			for(e = 1; e <= NumWaveGuides; e++) 
			for(j = 0; j < 3; j++) if(EXP[2*e-1][j] == Exp1) WGB[e] ++;
			}
		for(d = 1; d <= NumWaveGuides; d++) if(WGA[d] < 1)
			{
			if(Micro_Print == 1) printf("\n\nWon't look for (PP,SF) curves! Gen 'B' does not appear with any exponents also appearing in R1 or R2.");
			return(2);
			}		
		for(d = 1; d <= NumWaveGuides; d++) if(WGB[d] == 1) 
			{
			FB = TRUE;
			break;
			}
		}								
	
	/*********************************************************************************************** 
		Find the exponents traced by the 'first edge' of the band of edges meeting vertex 0,
		resp vertex 2, which come from the vertex following vertex 1, resp vertex 3, in cyclic 
		order around vertex 0, resp vertex 2. 
	**********************************************************************************************/
	
	for(vertex = NumStowed = 0; vertex <= 2; vertex += 2)
		{		
		vertex1 = FV[vertex];
		ss = A[vertex][vertex1];		
		while(vertex1 != (vertex + 1)) 
			{
			vertex1 = CO[vertex][vertex1];
			ss += A[vertex][vertex1];
			}			
		if(ss >= V[vertex]) ss -= V[vertex];
		
		
		/******************************************************************************************
			Start at edge e of vertex v and follow the path until arriving at a vertex != vertex.
		******************************************************************************************/
		
		v = vertex;
		e = ss;
		Exp1 = 0;		
		do
			{
			if(v & 1) w = v - 1;
			else w = v + 1;
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			++Exp1;
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}
			e = B[w][v] - e;
			}
		while(v == vertex);
	
		/* Check where Exp1 occurs in the list of generator exponents. */
	
		for(j = 0; j < 3; j++) if(Exp1 == EXP[vertex/2 + 9][j]) break;
		d = vertex/2 + 9;		
		switch(j)
			{
			case 0:
				NExp1 = NEX[d][0];
				NExp2 = NEX[d][2];
				NExp3 = NEX[d][1];
				Exp2  = EXP[d][2];
				Exp3  = EXP[d][1];			
				break;
			case 1:
				NExp1 = NEX[d][1];
				NExp2 = NEX[d][2];
				NExp3 = NEX[d][0];
				Exp2  = EXP[d][2];
				Exp3  = EXP[d][0];				
				break;		
			case 2:
				NExp1 = NEX[d][2];
				NExp2 = NEX[d][1];
				NExp3 = NEX[d][0];
				Exp2  = EXP[d][1];
				Exp3  = EXP[d][0];				
				break;			
			default:
				return(2);			
			}
					
		if(NExp1 > 0) 
			{
			if(W1)	DisposePtr((unsigned char*) W1);
			W1 = (unsigned char*) NewPtr((sizeof(char)*(NExp1+1)));
			if(W1 == NULL) Mem_Error();
			}
		if(NExp2 > 0) 
			{
			if(W2)	DisposePtr((unsigned char*) W2);
			W2 = (unsigned char*) NewPtr((sizeof(char)*(NExp2+1)));
			if(W2 == NULL) Mem_Error();
			}
		if(NExp3 > 0) 
			{
			if(W3)	DisposePtr((unsigned char*) W3);
			W3 = (unsigned char*) NewPtr((sizeof(char)*(NExp3+1)));
			if(W3 == NULL) Mem_Error();
			}
			
		MaxL = NExp1;
		if(NExp2 > MaxL) MaxL = NExp2;
		if(NExp3 > MaxL) MaxL = NExp3;	

		if(W4)	DisposePtr((unsigned char*) W4);
		W4 = (unsigned char*) NewPtr(4*MaxL+1);
		if(W4 == NULL) Mem_Error();
			
		/* Extract W1,W2,W3 from DualRelators[vertex/2 + 1]. */
	
		r = p = *DualRelators[vertex/2 + 1];
		p += ss;	
		if(NExp1)
			{
			for(length = 0, q = W1; length < NExp1; )
				{
				*q++ = *p++;
				if( (*p == EOS) ) p = r;
				length ++;
				}
			*q = EOS;
			}
		if(NExp2)
			{	
			for(length = 0, q = W2; length < NExp2; )
				{
				*q++ = *p++;
				if( (*p == EOS) ) p = r;
				length ++;
				}
			*q = EOS;
			}
		if(NExp3)
			{	
			for(length = 0, q = W3; length < NExp3; )
				{
				*q++ = *p++;
				if( (*p == EOS) ) p = r;
				length ++;
				}
			*q = EOS;
			}
				
		if(NExp3)
			{
			if(vertex == 0)
				{
				if(Micro_Print == 1)
					{
					printf("\n\nP = %u, Q = %u, R = %u",Exp3,Exp2,Exp1);
					printf("\n\nNExpR = %u, W1 = %s",NExp1,W1);
					printf("\n\nNExpQ = %u, W2 = %s",NExp2,W2);				
					printf("\n\nNExpP = %u, W3 = %s",NExp3,W3);
					printf("\n\nA^P Dual = W1W2 = %s%s",W1,W2);
					}
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 1;	
				NSEL[NumStowed] = Exp3;		
				Inverse(W3);
				if(Micro_Print == 1) printf("\n\nA^Q Dual = w3W1 = %s%s",W3,W1);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 2;
				NSEL[NumStowed] = Exp2;			
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nA^R Dual = w3w2 = %s%s",W3,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 3;
				NSEL[NumStowed] = Exp1;			
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nA^(P+Q) Dual = W1w3W1W2 = %s%s%s%s",W1,W3,W1,W2);
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = 2*NExp1 + NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 4;	
				NSEL[NumStowed] = Exp2 + Exp3;		
				Inverse(W3);
				if(Micro_Print == 1) printf("\n\nA^(P-R) Dual = W3W2W1W2 = %s%s%s%s",W3,W2,W1,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + 2*NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 5;	
				NSEL[NumStowed] = abs(Exp1 - Exp3);		
				Inverse(W1);
				if(Micro_Print == 1) printf("\n\nA^(Q+R) Dual = W3w1W3W2 = %s%s%s%s",W3,W1,W3,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + NExp2 + 2*NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 6;	
				NSEL[NumStowed] = Exp1 + Exp2;		
				}
			if(vertex == 2)
				{
				if(Micro_Print == 1)
					{
					printf("\n\nS = %u, T = %u, U = %u",Exp3,Exp2,Exp1);
					printf("\n\nNExpU = %u, W1 = %s",NExp1,W1);
					printf("\n\nNExpT = %u, W2 = %s",NExp2,W2);				
					printf("\n\nNExpS = %u, W3 = %s",NExp3,W3);
					printf("\n\nB^S Dual = W1W2 = %s%s",W1,W2);
					}
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 7;	
				NSEL[NumStowed] = Exp3;		 			
				Inverse(W3);
				if(Micro_Print == 1) printf("\n\nB^T Dual = w3W1 = %s%s",W3,W1);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 8;	
				NSEL[NumStowed] = Exp2;			
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nB^U Dual = w3w2 = %s%s",W3,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 9;	
				NSEL[NumStowed] = Exp1;			
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nB^(S+T) Dual = W1w3W1W2 = %s%s%s%s",W1,W3,W1,W2);
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = 2*NExp1 + NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 10;
				NSEL[NumStowed] = Exp2 + Exp3;			
				Inverse(W3);
				if(Micro_Print == 1) printf("\n\nB^(S-U) Dual = W3W2W1W2 = %s%s%s%s",W3,W2,W1,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + 2*NExp2 + NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 11;
				NSEL[NumStowed] = abs(Exp1 - Exp3);				
				Inverse(W1);
				if(Micro_Print == 1) printf("\n\nB^(T+U) Dual = W3w1W3W2 = %s%s%s%s",W3,W1,W3,W2);
				q = W4;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W3;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + NExp2 + 2*NExp3 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 12;
				NSEL[NumStowed] = Exp1 + Exp2;				
				}		
			}
			
		if(NExp3 == 0)
			{
			if(vertex == 0)
				{
				if(Micro_Print == 1)
					{
					printf("\n\nP = %u, R = %u",Exp2,Exp1);
					printf("\n\nNExpR = %u, W1 = %s",NExp1,W1);
					printf("\n\nNExpP = %u, W2 = %s",NExp2,W2);
					printf("\n\nA^P Dual = W1 = %s",W1);
					}
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 13;	
				NSEL[NumStowed] = Exp2;		
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nA^R Dual = w2 = %s",W2);
				q = W4;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 14;
				NSEL[NumStowed] = Exp1;		
				if(Micro_Print == 1) printf("\n\nA^(P+R) Dual = w2W1 = %s%s",W2,W1);
				q = W4;
				p = W2;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;			
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 15;	
				NSEL[NumStowed] = Exp1 + Exp2;		
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nA^(P-R) Dual = W1W2 = %s%s",W1,W2);
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 16;	
				NSEL[NumStowed] = abs(Exp1 - Exp2);
				if(FA)
					{
					if(Micro_Print == 1) printf("\n\nA^(2P-R) Dual = W1W1W2 = %s%s%s",W1,W1,W2);
					q = W4;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;				
					HS = 2*NExp1 + NExp2 + 1;
					Stow_Relators(W4,HS,++NumStowed);
					NSL[NumStowed] = 21;	
					NSEL[NumStowed] = abs(2*Exp2 - Exp1);					
					if(Micro_Print == 1) printf("\n\nA^(P-2R) Dual = W1W2W2 = %s%s%s",W1,W2,W2);
					q = W4;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;				
					HS = NExp1 + 2*NExp2 + 1;
					Stow_Relators(W4,HS,++NumStowed);
					NSL[NumStowed] = 22;	
					NSEL[NumStowed] = abs(2*Exp1 - Exp2);
					}
				}
			if(vertex == 2)
				{
				if(Micro_Print == 1)
					{
					printf("\n\nS = %u, U = %u",Exp2,Exp1);
					printf("\n\nNExpU = %u, W1 = %s",NExp1,W1);
					printf("\n\nNExpS = %u, W2 = %s",NExp2,W2);
					printf("\n\nB^S Dual = W1 = %s",W1);
					}
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				HS = NExp1 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 17;	
				NSEL[NumStowed] = Exp2;		
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nB^U Dual = w2 = %s",W2);
				q = W4;
				p = W2;
				while( (*q++ = *p++) ) ;
				HS = NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 18;
				NSEL[NumStowed] = Exp1;		
				if(Micro_Print == 1) printf("\n\nB^(S+U) Dual = w2W1 = %s%s",W2,W1);
				q = W4;
				p = W2;
				while( (*q++ = *p++) ) ;
				q--;
				p = W1;
				while( (*q++ = *p++) ) ;			
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 19;	
				NSEL[NumStowed] = Exp1 + Exp2;		
				Inverse(W2);
				if(Micro_Print == 1) printf("\n\nB^(S-U) Dual = W1W2 = %s%s",W1,W2);
				q = W4;
				p = W1;
				while( (*q++ = *p++) ) ;
				q--;
				p = W2;
				while( (*q++ = *p++) ) ;				
				HS = NExp1 + NExp2 + 1;
				Stow_Relators(W4,HS,++NumStowed);
				NSL[NumStowed] = 20;	
				NSEL[NumStowed] = abs(Exp1 - Exp2);				
				if(FB)
					{
					if(Micro_Print == 1) printf("\n\nB^(2S-U) Dual = W1W1W2 = %s%s%s",W1,W1,W2);
					q = W4;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;				
					HS = 2*NExp1 + NExp2 + 1;
					Stow_Relators(W4,HS,++NumStowed);
					NSL[NumStowed] = 23;	
					NSEL[NumStowed] = abs(2*Exp2 - Exp1);					
					if(Micro_Print == 1) printf("\n\nB^(S-2U) Dual = W1W2W2 = %s%s%s",W1,W2,W2);
					q = W4;
					p = W1;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;
					q--;
					p = W2;
					while( (*q++ = *p++) ) ;				
					HS = NExp1 + 2*NExp2 + 1;
					Stow_Relators(W4,HS,++NumStowed);
					NSL[NumStowed] = 24;	
					NSEL[NumStowed] = abs(2*Exp1 - Exp2);					
					}
				}		
			}			
		}
				
	if(W1)	DisposePtr((unsigned char*) W1);
	if(W2)	DisposePtr((unsigned char*) W2);
	if(W3)	DisposePtr((unsigned char*) W3);
	if(W4)	DisposePtr((unsigned char*) W4);
	
	return(Set_Up_SF_Check(NumStowed,NSL,NSEL,F1,F2));
}

int Stow_Relators(unsigned char* MyPtr,unsigned int HS,int i)
{
	unsigned char	*p,
					*q;
					
	if(Copy_Of_Rel_3[i] != NULL) DisposeHandle((char **) Copy_Of_Rel_3[i]);
	Copy_Of_Rel_3[i] = (unsigned char **) NewHandle(HS);
	if(Copy_Of_Rel_3[i] == NULL) Mem_Error();
	p = MyPtr;
	q = *Copy_Of_Rel_3[i];
	while( (*q++ = *p++) ) ;	

	return(0);	
}

int Set_Up_SF_Check(int NumStowed,unsigned char* NSL,unsigned int* NSEL,char F1,char F2)
{
	char			F3;
	
	unsigned char	*p,
					*q;
					
	int				i,
					j;			
	
	for(i = 1,j = 0; i <= NumStowed; i++)
		{				
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Rel_3[i]));	
		if(Relators[1] == NULL) Mem_Error();
		p = *Copy_Of_Rel_3[i];
		q = *Relators[1];
		while( (*q++ = *p++) ) ;
		NumRelators = 1;
		NumGenerators = 2;
		if(Freely_Reduce()) continue;
		B10B11Recognized = FALSE;
		F3 = FALSE;
		if(F2 != 3 && F1 && (Genus_Two_Seifert_Fibered(1,2) == 13)) F3 = TRUE;
		if(F2 == 3 && F1 && (Genus_Two_Seifert_Fibered(1,3) == 13)) F3 = TRUE;
		if(!F1 && Look_For_Disjoint_Genus_2_Curves(F2)) F3 = TRUE;
		if(F2 == 3 && F3) j++;
		if(F2 != 3 && F3) 
			{
			j++;
			Translate_2_Dual_Pres(*Copy_Of_Rel_3[i]);
			printf(" where R is %s, ",*Copy_Of_Rel_3[i]);
			printf("which is the dual of the proper-power ");
			switch(NSL[i])
				{
				case 1: 
					printf("A^%u.",NSEL[i]);
					break;
				case 2: 
					printf("A^%u.",NSEL[i]);
					break;				
				case 3:
					printf("A^%u.",NSEL[i]);
					break;				
				case 4:
					printf("A^%u.",NSEL[i]);
					break;				
				case 5:
					printf("A^%u.",NSEL[i]);
					break;
				case 6:
					printf("A^%u.",NSEL[i]);
					break;					
				case 7:
					printf("B^%u.",NSEL[i]);
					break;					
				case 8:
					printf("B^%u.",NSEL[i]);
					break;					
				case 9:
					printf("B^%u.",NSEL[i]);
					break;					
				case 10:
					printf("B^%u.",NSEL[i]);
					break;					
				case 11:
					printf("B^%u.",NSEL[i]);
					break;
				case 12:
					printf("B^%u.",NSEL[i]);
					break;	
				case 13:
					printf("A^%u.",NSEL[i]);
					break;	
				case 14:
					printf("A^%u.",NSEL[i]);
					break;	
				case 15:
					printf("A^%u.",NSEL[i]);
					break;						
				case 16:
					printf("A^%u.",NSEL[i]);
					break;						
				case 17:
					printf("B^%u.",NSEL[i]);
					break;						
				case 18:
					printf("B^%u.",NSEL[i]);
					break;						
				case 19:
					printf("B^%u.",NSEL[i]);
					break;						
				case 20:
					printf("B^%u.",NSEL[i]);
					break;																												
				}
			}
		}
	
	if(F1)
		{
		if(j == 0) return(7);
	
		if(j > 0) 
			{
			if(F2 == 3) return(5);
			printf("\n\nHeegaard found a (PP,SF) curve in the Heegaard surface. If there are also (SF,PP) curves disjoint from (PP,SF) curves,");
			printf(" this manifold may have more than one Heegaard splitting.");
			return(5);	
			}
		}
	if(!F1)
		{
		if(j == 0) 
			{
			if(F2 == 3) return(6);
			printf("\n\nThere are no disjoint curves.");
			return(6);
			}
				
		if(j > 0) 
			{
			if(F2 == 3) return(8);
			printf("\n\nHeegaard found a disjoint curve in the Heegaard surface; so this is a distance 2 splitting and");
			printf("\nthe manifold may have more than one Heegaard splitting.");
			return(8);				
			}
		}		
	return(0);	
}

void Translate_2_Dual_Pres(unsigned char* MyPtr)
{
	unsigned char	*p,
					x;
					
	p = MyPtr;
	while(1) 
		{
		x = *p;
		if(x == EOS) break;
		switch(x)
			{
			case 'A':
				*p = 'X';
				break;
			case 'a':
				*p = 'x';
				break;
			case 'B':
				*p = 'Y';
				break;
			case 'b':
				*p = 'y';
				break;
			}	
		p++;	
		}	
}

int Look_For_Disjoint_Genus_2_Curves(char F1)
{
	unsigned char	*p,
					x;
					
	/************************************************************************************
		This routine is called when Universal Minimizers exist and a dual curve in H' 
		of a proper-power in H might be primitive or a proper-power in H'. Such curves
		are the only possible 'disjoint curves' when Universal Minimizers exist.
	************************************************************************************/

	Length = GetHandleSize((char**) Relators[1]) - 1;
	NumRelators = 1; 

	/****************************************************************** 
		Check if Relators[1] is already a primitive or proper-power. 
	******************************************************************/
	
	p = *Relators[1];
	x = *p;
	if(x) 
		{
		while( (x == *p)  ) p++;
		if(*p == EOS) 
			{
			if(F1 != 3) printf("\nR is primitive or a proper-power,");
			return(1);
			}
		}
	
	SLength = Length;		
	if(Find_Flow_A(NORMAL,FALSE) && Length < SLength) 
		{
		if(F1 != 3) printf("\nR is primitive or a proper-power,");
		return(1);
		}
	return(0);
}