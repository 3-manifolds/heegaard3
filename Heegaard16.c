#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <ctype.h>

/****************************** Functions in Heegaard16.c **********************************
L   13 Compute_Homology(char Flag1)
L  391 gcd(unsigned long a,unsigned long b)
L  405 Prune_Search_Tree(void)
********************************************************************************************/

#define A_BIG_NUMBER 2147483645

unsigned long Compute_Homology(char Flag1)
{
	/******************************************************************************************
		This routine computes the integral first homology of the presentation in Relators[].
	******************************************************************************************/
		
	unsigned char 	*p,
					x;
					
	int				All_Zeros,
					i,
					j,
					Num_Torsion_Values,
					Pivot_Column,
					Pivot_Row,	
					S_Num_Torsion_Values,
					SNumGenerators,
					SNumRelators;
					
	long			*M[MAXNUMRELATORS],
					Mij,
					Min_Abs,
					Mult,
					*ptr = NULL,
					Previous_Min_Abs,
					Temp,
					*temp;
					
	unsigned long	*Torsion = NULL,
					TorsionProduct = 1;
					
	unsigned long 	gcd();				
	
	/******************************************************************************************
					Get some storage for the matrix M[][] and the array Torsion.
	******************************************************************************************/
		
	for(i = 0; i < NumRelators; i++)
		{
		M[i] = (long *)NewPtr(sizeof(long)*NumGenerators);
		if(M[i] == NULL) Mem_Error();
		}	
	Torsion = (unsigned long *)NewPtr(sizeof(long)*NumGenerators);
	if(Torsion == NULL) Mem_Error();
															
	/******************************************************************************************
					Abelianize the relators and save the results in M[][].
	******************************************************************************************/	
	
	ptr = (long *)NewPtr(sizeof(long)*125);
	if(ptr == NULL) Mem_Error();
	for(i = 0; i < NumRelators; i++)
		{
		for(j = 64 + NumGenerators; j >= 65; j--) ptr[j] = 0L;
		for(j = 96 + NumGenerators; j >= 97; j--) ptr[j] = 0L;
		p = *Relators[i+1];
		while( (x = *p++) ) ptr[x] ++;
		for(j = 0; j < NumGenerators; j++) M[i][j] = ptr[j + 65] - ptr[j + 97];
		}
		
	DisposePtr((long *) ptr);
	
	/******************************************************************************************
							Diagonalize the matrix M[][].
	******************************************************************************************/				
	
	SNumGenerators 			= NumGenerators;
	SNumRelators 			= NumRelators;
	Num_Torsion_Values 		= 0;
	S_Num_Torsion_Values 	= 0;
	Betti_Number			= 0;
	
	while(1)
		{
		/**************************************************************************************
			Look for some nonzero element of M[][] to serve as an initial pivot element.
		**************************************************************************************/
		
		Min_Abs = A_BIG_NUMBER;
		if(SNumRelators)
			do
				{
				i = SNumRelators - 1;
				for(j = 0; j < SNumGenerators; j++) if(M[i][j])
					{
					Mij = M[i][j];
					if(Mij > 0)
						Min_Abs = Mij;
					else
						Min_Abs = -Mij;	
					Pivot_Row = i;
					Pivot_Column = j;
					break;
					}
				if(Min_Abs == A_BIG_NUMBER) SNumRelators --;
				}
			while(SNumRelators && Min_Abs == A_BIG_NUMBER);	
		
		if(Min_Abs == A_BIG_NUMBER)
			{
			/**********************************************************************************
				If Min_Abs = A_BIG_NUMBER, M[][] contains no nonzero elements. Set the 
				Betti_Number of the presentation equal to NumGenerators - Num_Torsion_Values
				- S_Num_Torsion_Values, then break out of this loop and report results.
			**********************************************************************************/	
			
			Betti_Number = NumGenerators - Num_Torsion_Values - S_Num_Torsion_Values;
			break;
			}	
_BEGIN:	
		/**************************************************************************************
			Starting from the current pivot element,look for a nonzero element of M[][]
			which is minimal, both in its row and in its column, to serve as the new pivot
			element.
		**************************************************************************************/
		
		do
			{
			Previous_Min_Abs = Min_Abs;
			
			/**********************************************************************************
								Search the current Pivot_Column of M[][].
			**********************************************************************************/
			
			for(i = 0; i < SNumRelators; i++)
				{
				Mij = M[i][Pivot_Column];
				if(Mij && (Mij > -Min_Abs) && (Mij < Min_Abs))
					{
					if(Mij > 0)
						Min_Abs = Mij;
					else
						Min_Abs = -Mij;	
					Pivot_Row = i;
					if(Min_Abs == 1) break;
					}	
				}
				
			/**********************************************************************************
								Search the current Pivot_Row of M[][].
			**********************************************************************************/		
			
			for(j = 0; j < SNumGenerators; j++)
				{
				Mij = M[Pivot_Row][j];
				if(Mij && (Mij > -Min_Abs) && (Mij < Min_Abs))
					{
					if(Mij > 0)
						Min_Abs = Mij;
					else
						Min_Abs = -Mij;	
					Pivot_Column = j;
					if(Min_Abs == 1) break;
					}	
				}	
			}
		while(Previous_Min_Abs > Min_Abs && Min_Abs > 1);
		
		/**************************************************************************************
			Add the appropriate multiple of the Pivot_Column to each column of M[][] with
			a nonzero entry in Pivot_Row.	
		**************************************************************************************/
		
		for(j = 0; j < SNumGenerators; j++) if(M[Pivot_Row][j] && j != Pivot_Column)
			{
			Mult = M[Pivot_Row][j]/Min_Abs;
			if(M[Pivot_Row][Pivot_Column] < 0) Mult = -Mult;
			for(i = 0; i < SNumRelators; i++) if(M[i][Pivot_Column])
			M[i][j] -= Mult*M[i][Pivot_Column];
			}
			
		/**************************************************************************************
			Add the appropriate multiple of the Pivot_Row to each row of M[][] with
			a nonzero entry in Pivot_Column.	
		**************************************************************************************/
		
		for(i = 0; i < SNumRelators; i++) if(M[i][Pivot_Column] && i != Pivot_Row)
			{
			Mult = M[i][Pivot_Column]/Min_Abs;
			if(M[Pivot_Row][Pivot_Column] < 0) Mult = -Mult;
			for(j = 0; j < SNumGenerators; j++) if(M[Pivot_Row][j])
			M[i][j] -= Mult*M[Pivot_Row][j];
			}
		
		/**************************************************************************************
			Check whether every element of M[][] in the Pivot_Row or Pivot_Column except
			M[Pivot_Row][Pivot_Column] is now zero.
		**************************************************************************************/
		
		All_Zeros = TRUE;
		if(Min_Abs > 1)
			{
			for(i = 0; i < SNumRelators; i++) if(M[i][Pivot_Column] && i != Pivot_Row)
				{
				All_Zeros = FALSE;
				break;
				}
				
			if(All_Zeros == TRUE)
			for(j = 0; j < SNumGenerators; j++) if(M[Pivot_Row][j] && j != Pivot_Column)
				{
				All_Zeros = FALSE;
				break;
				}
			}
		
		if(All_Zeros == TRUE)
			{
			/**********************************************************************************
				Swap the Pivot_Row of M[][] with the last row of M[][] and decrement the
				number of rows of M[][].
			**********************************************************************************/
			
			SNumRelators --;
			temp = M[SNumRelators];
			M[SNumRelators] = M[Pivot_Row];
			M[Pivot_Row] = temp;
		
			/**********************************************************************************
				Swap the Pivot_Column of M[][] with the last column of M[][] and decrement
				the number of columns of M[][].
			**********************************************************************************/
			
			SNumGenerators --;
			for(i = 0; i <= SNumRelators; i++)
				{
				Temp = M[i][SNumGenerators];
				M[i][SNumGenerators] = M[i][Pivot_Column];
				M[i][Pivot_Column] = Temp;
				}
			
			/**********************************************************************************
									Save Min_Abs as a torsion value.
			**********************************************************************************/
			
			if(Num_Torsion_Values)
				{
				for(i = Num_Torsion_Values - 1; i >= 0; i--)
					{
					Temp = gcd(Torsion[i],Min_Abs);
					Torsion[i+1] = Temp;
					if(Temp == Min_Abs) break;
					if(2*(unsigned int)A_BIG_NUMBER/Torsion[i] < Min_Abs/Temp)
						{
						if(Batch == FALSE) SysBeep(5);
						printf("\n\nA Torsion value is greater than 4,294,967,290. ");
						printf("This is an overflow. Sorry!");
						goto END;
						}
					Torsion[i] *= Min_Abs/Temp;
					Min_Abs = Torsion[i];
					}
				if(Torsion[Num_Torsion_Values] == 1)
					S_Num_Torsion_Values ++;
				else
					Num_Torsion_Values ++;		
				}
			else
				{
				if(Min_Abs == 1)
					S_Num_Torsion_Values ++;
				else
					{	
					Torsion[0] = Min_Abs;
					Num_Torsion_Values = 1;
					}
				}
			}
		else
			goto _BEGIN;									
		}
		
	/******************************************************************************************
									Print the results.
	******************************************************************************************/
		
		S_Num_Torsion_Values = Num_Torsion_Values;
		if(Flag1 == TRUE)
			{
			if(S_Num_Torsion_Values == 0) 
				{
				TorsionProduct = 0;
				goto END;
				}
			else while(1)
				{
				TorsionProduct *= Torsion[--S_Num_Torsion_Values];
				if(S_Num_Torsion_Values == 0) goto END;
				}
			}	
		
		if(Batch == 6 && H_Results != NULL) fprintf(H_Results,"\n\n%s ",PresName);
		if(Betti_Number == 0)
			{
			 if(Num_Torsion_Values == 0)
				{
				if(Batch == 6) 
					{
					printf("\nH_1 = 1");
					if(H_Results != NULL) fprintf(H_Results,"H_1 = 1");
					}	
				else 
					{
					if(Flag1 != 2) printf("\n\n");
					printf("The homology is: Z/1");
					}
				}
			else
				{
				if(Batch == 6)
					{
					printf("\nH_1 = ");
					if(H_Results != NULL) fprintf(H_Results,"H_1 = ");
					}
				else 
					{
					if(Flag1 != 2) printf("\n\n");
					printf("The homology is: ");
					}
				
				while(Num_Torsion_Values)
					{	
					printf("Z/%lu ",Torsion[--Num_Torsion_Values]);
					if(Batch == 6 && H_Results != NULL) fprintf(H_Results,"Z/%lu ",Torsion[Num_Torsion_Values]);
					if(Num_Torsion_Values == 0) break;
					printf("+ ");
					if(Batch == 6 && H_Results != NULL) fprintf(H_Results,"+ ");	
					}
				}	
			}
		else
			{
			if(Batch == 6) 
				{
				if(Betti_Number == 1) 
					{
					printf("\nH_1 = Z ");
					if(H_Results != NULL) fprintf(H_Results,"H_1 = Z ");
					}
				else 
					{
					printf("\nH_1 = %dZ ",Betti_Number);
					if(H_Results != NULL) fprintf(H_Results,"H_1 = %dZ ",Betti_Number);
					}
				}
			else 
				{
				if(Betti_Number == 1) 
					{
					if(Flag1 != 2) printf("\n\n");
					printf("The homology is: Z ");
					if(H_Results != NULL) fprintf(H_Results,"H_1 = Z ");
					}			
				else 
					{
					if(Flag1 != 2) printf("\n\n");
					printf("The homology is: %dZ ",Betti_Number);
					if(H_Results != NULL) fprintf(H_Results,"H_1 = %dZ ",Betti_Number);
					}
				}
			while(Num_Torsion_Values) 
				{
				printf("+ Z/%lu ",Torsion[--Num_Torsion_Values]);
				if(H_Results != NULL) fprintf(H_Results,"+ Z/%lu ",Torsion[Num_Torsion_Values]);
				}
			}
	END:
								
	/******************************************************************************************
				Free the memory used by the array M[][] and the array Torsion[].
	******************************************************************************************/
		
	for(i = 0; i < NumRelators; i++) if(M[i]) DisposePtr((char *) M[i]);
	DisposePtr((char *) Torsion);
	
	return(TorsionProduct);
}

unsigned long int gcd(unsigned long a,unsigned long b)
{
	if(a == 0L) return(b);
	do
		{
		if((b = b%a) == 0)
			return(a);
		if((a = a%b) == 0)
			return(b);
		}
	while(1);			
}	

#ifdef PRUNE_SEARCH_TREE
void Prune_Search_Tree(void)
{
	unsigned char	*ptr = NULL;
					
	int				Ancestor,
					Dad,
					*DesL = NULL,
					h,
					i,
					j,
					NumDel;
	
	ptr = (unsigned char *) NewPtr(100);
	if(ptr == NULL) Mem_Error();
	DesL = (int *) NewPtr(sizeof(int)*MAX_SAVED_PRES);
	if(Desl == NULL) Mem_Error();
	DO_MORE:
	printf("\n\nLIST THE NUMBER OF ACTIVE DESCENDANTS OF EACH PRESENTATION ?  HIT 'y' OR 'n'.    ");
	GET_RESPONSE1:	
	switch(WaitkbHit())
		{
		case 'y':
			for(i = 0; i < NumFilled; i++) DesL[i] = 0;
			for(i = NumFilled - 1; i > 0; i--)
				{
				DesL[FR[i]] += DesL[i];
				if(UDV[i] < DONE) DesL[FR[i]] ++;
				}
			for(i = 0; i < NumFilled; i++) if(UDV[i] < DONE) DesL[i] ++;	
			j = 0;
			j += printf("\nPres  :");	
			for(i = h = 0; i < NumFilled; i++)
				{
				if(j > 85)
					{
					printf("\nNumDes:");
					for( ; h < i; h++) printf("%4d",DesL[h]);
					if(i < NumFilled)
						{
						j = 0;
						j += printf("\nPres  :");						
						}
					}
				j += printf("%4d",i+1);
				}
			if(h < i)
				{	
				printf("\nNumDes:");
				for( ; h < i; h++) printf("%4d",DesL[h]);
				}				
			break;	
		case 'n':
			break;
		default:
			if(Batch == FALSE) SysBeep(5);
			goto GET_RESPONSE1;
		}
	printf("\n\nCURRENT PRESENTATIONS RANGE FROM NUMBER 1 TO NUMBER %u. ENTER THE NUMBER OF A PRESENTATION,",NumFilled);	
	printf("\nWHOSE PROPER DESCENDANTS YOU WANT Heegaard TO STOP SEARCHING, AND HIT 'return'.    ");
	GET_RESPONSE2:
	Ancestor = 0;		
	ReadString((char *)ptr, GetPtrSize(ptr));
	sscanf((char *) ptr,"%d",&Ancestor);
	if(Ancestor < 1 || Ancestor > NumFilled)
		{
		if(Batch == FALSE) SysBeep(5);
		goto GET_RESPONSE2;
		}
		
	Ancestor --;
	NumDel = 0;			
	for(i = NumFilled - 1; i > Ancestor; i--) if(UDV[i] < DONE)
		{
		for(Dad = FR[i]; Dad > Ancestor; Dad = FR[Dad]) ;
		if(Dad == Ancestor)
			{
			if(UDV[i] < DONE) UDV[i] = DONE;
			NumDel ++;
			}
		}
		
	if(NumDel)
		printf("\n\nMade %d currently active proper descendant(s) of Presentation %d inactive.",
			NumDel,Ancestor + 1);
	else
		printf("\n\nNo proper descendants of Presentation %d are currently active.",Ancestor + 1);
		
	printf("\n\nDO MORE PRUNNING ? HIT 'y' OR 'n'.    ");
	GET_RESPONSE3:	
	switch(WaitkbHit())
		{
		case 'y':
			goto DO_MORE;
		case 'n':
			break;
		default:
			if(Batch == FALSE) SysBeep(5);
			goto GET_RESPONSE3;
		}
	DisposePtr((char *) ptr);
	DisposePtr((char *) DesL);
}
#endif
