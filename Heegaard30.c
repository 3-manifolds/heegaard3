#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <string.h>

/*
Remark!
The routines in this file are a work in progress which will eventually replace the
recognition routines Heegaard currently uses to recognize most toroidal manifolds.
*/

char 			ToroidalR = FALSE;
			                                           
unsigned char 	*ptr301 = NULL,
                *ptr302 = NULL;

int Genus_Two_Meridian_Reps2(int OrbitNum, int Flag)
{
    /******************************************************************************************
    	Genus_Two_Meridian_Reps2() can be used to find the canonical representatives of the
        'meridians' of a manifold M1 = H[Relators[1]] or M2 = H[Relators[2]]. 
  			The routine requires that H[Relators[1] U Relators[2]] is uniquely determined by 
  		Relators[1] U Relators[2]. In particular, the routine will work when one or both of 
  		the generators of H appear in Relators[1] or Relators[2] only with exponents having 
  		only one absolute value e >= 2.	
    ******************************************************************************************/
 
     char			BadR1,
    				BadR2,
    				ExpA1Plus,
    				ExpA1Neg,
    				ExpB1Plus,
    				ExpB1Neg,
					ExpA2Plus,
    				ExpA2Neg,
    				ExpB2Plus,
    				ExpB2Neg,
    				R1APP,
    				R1BPP,
    				R2APP,
    				R2BPP;
    				
    unsigned char	*p,
    				*q,
    				**Temp;				
    
    int           	i,
                    MaxR1AExp,
                    MaxR1BExp,
                    MaxR2AExp,
                    MaxR2BExp,
                    ReturnValue;
    
    unsigned long   HS,
    				HS1,
    				HS2,
    				L1,
    				L2;
    				
    if(Genus_Two_Meridian_Reps2_S3(Flag)) return(1);				    

	if(Check_Freely_Reduced_Dual_Presentation()) 
		{
printf("\n\nThe Dual Presentation is not freely reduced.");
		return(68);
		}
		
	if(Get_Genus_2_EXPS()) return(69);
	
	/*
	printf("\n");	
	for(i = 0; i < 6; i++) printf(" EXPA1_SF[%d] = %3d",i,EXPA1_SF[i]);
	printf("\n");
	for(i = 0; i < 6; i++) printf(" EXPB1_SF[%d] = %3d",i,EXPB1_SF[i]);
	printf("\n");
	for(i = 0; i < 6; i++) printf(" EXPA2_SF[%d] = %3d",i,EXPA2_SF[i]);
	printf("\n");
	for(i = 0; i < 6; i++) printf(" EXPB2_SF[%d] = %3d",i,EXPB2_SF[i]);	
	*/
	
	/*	Find the maximal absolute value of the exponents with which each generator appears in each relator.	*/
		
	for(i = MaxR1AExp = 0; i < 6; i++) if(abs(EXPA1_SF[i]) > MaxR1AExp) MaxR1AExp = abs(EXPA1_SF[i]);
	if(MaxR1AExp == 0) return(70);
	for(i = MaxR1BExp = 0; i < 6; i++) if(abs(EXPB1_SF[i]) > MaxR1BExp) MaxR1BExp = abs(EXPB1_SF[i]);
	if(MaxR1BExp == 0) return(70);
	for(i = MaxR2AExp = 0; i < 6; i++) if(abs(EXPA2_SF[i]) > MaxR2AExp) MaxR2AExp = abs(EXPA2_SF[i]);
	if(MaxR2AExp == 0) return(70);	
	for(i = MaxR2BExp = 0; i < 6; i++) if(abs(EXPB2_SF[i]) > MaxR2BExp) MaxR2BExp = abs(EXPB2_SF[i]);
	if(MaxR2BExp == 0) return(70);
/*	
printf("\n\nMaxR1AExp = %d, MaxR1BExp = %d, MaxR2AExp = %d, MaxR2BExp = %d",MaxR1AExp,MaxR1BExp,MaxR2AExp,MaxR2BExp);	
*/
	/*** Check if a generator appears only with exponents ±e with e > 1. ***/
	
	R1APP = R1BPP = R2APP = R2BPP = FALSE;
	if(MaxR1AExp > 1 && abs(EXPA1_SF[0]) == MaxR1AExp && EXPA1_SF[1] == 0) R1APP = TRUE;
	if(MaxR1BExp > 1 && abs(EXPB1_SF[0]) == MaxR1BExp && EXPB1_SF[1] == 0) R1BPP = TRUE;
	if(MaxR2AExp > 1 && abs(EXPA2_SF[0]) == MaxR2AExp && EXPA2_SF[1] == 0) R2APP = TRUE;
	if(MaxR2BExp > 1 && abs(EXPB2_SF[0]) == MaxR2BExp && EXPB2_SF[1] == 0) R2BPP = TRUE;	
	if(MaxR1AExp > 1 && abs(EXPA1_SF[0]) == MaxR1AExp && abs(EXPA1_SF[1]) == MaxR1AExp && EXPA1_SF[2] == 0) R1APP = TRUE;
	if(MaxR1BExp > 1 && abs(EXPB1_SF[0]) == MaxR1BExp && abs(EXPB1_SF[1]) == MaxR1BExp && EXPB1_SF[2] == 0) R1BPP = TRUE;
	if(MaxR2AExp > 1 && abs(EXPA2_SF[0]) == MaxR2AExp && abs(EXPA2_SF[1]) == MaxR2AExp && EXPA2_SF[2] == 0) R2APP = TRUE;
	if(MaxR2BExp > 1 && abs(EXPB2_SF[0]) == MaxR2BExp && abs(EXPB2_SF[1]) == MaxR2BExp && EXPB2_SF[2] == 0) R2BPP = TRUE;
	
	/********************************************************************************************************
	 	If no generator appears in a relator R only with exponents ±e with e > 1, and each generator 
	 	appears in R with max exponents > 2, then R is not disjoint from a proper-power, and R is also
	 	not disjoint from a non-separating annulus whose boundary components are primitives.
	********************************************************************************************************/
	
	BadR1 		= TRUE;
	BadR2 		= TRUE;
	ToroidalR 	= FALSE;
	if(R1APP || R1BPP) BadR1 = FALSE;
	if(R2APP || R2BPP) BadR2 = FALSE;
	if(MaxR1AExp < 3 || MaxR1BExp < 3) BadR1 = FALSE;
	if(MaxR2AExp < 3 || MaxR2BExp < 3) BadR2 = FALSE;
	if(BadR1 && BadR2) 
	{
printf("\n\nL227 BadR1 & BadR2.");	
	return(71);
	}

	/** This is perhaps a good time to stow copies of Relators[1] and Relators[2] in Relators[21] and Relators[22]. **/

	for(i = 1; i <= 2; i++)
		{
		if(Relators[i + 20] != NULL) DisposeHandle((char **) Relators[i + 20]);
		Relators[i + 20] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i])); 
		if(Relators[i + 20] == NULL) Mem_Error();
		p = *Relators[i];
		q = *Relators[i + 20];    
		while( (*q++ = *p++) ) ;
		}
		
	HS1 = GetHandleSize((char **) Relators[1]);
	HS2 = GetHandleSize((char **) Relators[2]);
				      
	HS = HS1;
	if(HS1 < HS2) HS = HS2;		
	ptr301 = (unsigned char *) NewPtr(HS);
	if(ptr301 == NULL) Mem_Error();
	ptr302 = (unsigned char *) NewPtr(HS);
	if(ptr302 == NULL) Mem_Error();	
                    	
	for(i = 0, ExpA1Plus = FALSE; i < 6; i++) if(EXPA1_SF[i] > 0) { ExpA1Plus = TRUE; break; }
	for(i = 0, ExpA1Neg  = FALSE; i < 6; i++) if(EXPA1_SF[i] < 0) { ExpA1Neg  = TRUE; break; }
	for(i = 0, ExpB1Plus = FALSE; i < 6; i++) if(EXPB1_SF[i] > 0) { ExpB1Plus = TRUE; break; }
	for(i = 0, ExpB1Neg  = FALSE; i < 6; i++) if(EXPB1_SF[i] < 0) { ExpB1Neg  = TRUE; break; }
	for(i = 0, ExpA2Plus = FALSE; i < 6; i++) if(EXPA2_SF[i] > 0) { ExpA2Plus = TRUE; break; }
	for(i = 0, ExpA2Neg  = FALSE; i < 6; i++) if(EXPA2_SF[i] < 0) { ExpA2Neg  = TRUE; break; }
	for(i = 0, ExpB2Plus = FALSE; i < 6; i++) if(EXPB2_SF[i] > 0) { ExpB2Plus = TRUE; break; }
	for(i = 0, ExpB2Neg  = FALSE; i < 6; i++) if(EXPB2_SF[i] < 0) { ExpB2Neg  = TRUE; break; }	
	
	if(ToroidalR <= 0 && !BadR1 && ExpA1Plus && ExpA1Neg) Init_Genus_Two_Meridian_Reps2_S1(1,1,0,HS,HS1,HS2);
	if(ToroidalR <= 0 && !BadR1 && ExpB1Plus && ExpB1Neg && (!ExpA1Plus || !ExpA1Neg)) Init_Genus_Two_Meridian_Reps2_S1(1,2,0,HS,HS1,HS2);
	
	if(ToroidalR <= 0 && !BadR1 && MaxR1AExp > 1 && MaxR1BExp > 1)
		{
		if( ExpA1Plus && !ExpA1Neg &&  ExpB1Plus && !ExpB1Neg) Init_Genus_Two_Meridian_Reps2_S1(1,0,1,HS,HS1,HS2);
		if( ExpA1Plus && !ExpA1Neg && !ExpB1Plus &&  ExpB1Neg) Init_Genus_Two_Meridian_Reps2_S1(1,0,2,HS,HS1,HS2);
		if(!ExpA1Plus &&  ExpA1Neg &&  ExpB1Plus && !ExpB1Neg) Init_Genus_Two_Meridian_Reps2_S1(1,0,2,HS,HS1,HS2);
		if(!ExpA1Plus &&  ExpA1Neg && !ExpB1Plus &&  ExpB1Neg) Init_Genus_Two_Meridian_Reps2_S1(1,0,1,HS,HS1,HS2);
		}
	
	if(ToroidalR < 0) ToroidalR = 0;
	
	if(ToroidalR <= 0 && !BadR2 && ExpA2Plus && ExpA2Neg) Init_Genus_Two_Meridian_Reps2_S1(2,1,0,HS,HS1,HS2);
	if(ToroidalR <= 0 && !BadR2 && ExpB2Plus && ExpB2Neg &&(!ExpA2Plus || !ExpA2Neg)) Init_Genus_Two_Meridian_Reps2_S1(2,2,0,HS,HS1,HS2);
	
	if(ToroidalR <= 0 && !BadR2 && MaxR2AExp > 1 && MaxR2BExp > 1)
		{
		if( ExpA2Plus && !ExpA2Neg &&  ExpB2Plus && !ExpB2Neg) Init_Genus_Two_Meridian_Reps2_S1(2,0,1,HS,HS1,HS2);
		if( ExpA2Plus && !ExpA2Neg && !ExpB2Plus &&  ExpB2Neg) Init_Genus_Two_Meridian_Reps2_S1(2,0,2,HS,HS1,HS2);
		if(!ExpA2Plus &&  ExpA2Neg &&  ExpB2Plus && !ExpB2Neg) Init_Genus_Two_Meridian_Reps2_S1(2,0,2,HS,HS1,HS2);
		if(!ExpA2Plus &&  ExpA2Neg && !ExpB2Plus &&  ExpB2Neg) Init_Genus_Two_Meridian_Reps2_S1(2,0,1,HS,HS1,HS2);
		}
		
	/** At this point, if ToroidalR = FALSE, the only possibility is that one of Relators[1] or Relators[2] is positive. */
	
	if(!ToroidalR)
		{
		/** Check if Relators[1] or Relators[2] is positive. **/
		
		NumRelators = 1;
		if(Check_R1_Positivity() != 1) BadR1 = TRUE;
		Temp = Relators[1];
		Relators[1] = Relators[2];
		Relators[2] = Temp;
		if(Check_R1_Positivity() != 1) BadR2 = TRUE;
		NumRelators = 2;
	
		/** Restore Relators[1] and Relators[2]. **/
	
		for(i = 1; i <= 2; i++)
			{
			if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
			Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
			if(Relators[i] == NULL) Mem_Error();
			p = *Relators[i + 20];
			q = *Relators[i];    
			while( (*q++ = *p++) ) ;
			}
	
		if(BadR1 && BadR2) 
			{
		printf("\n\nL341 BadR1 & BadR2. ==> Can't find a toroidal presentation here.");
			ReturnValue = 72;
			goto END;
			}
		}
		
	switch(ToroidalR)
		{
		case 0:
			if(!BadR1)
				{
				for(i = 1; i <= 2; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
					if(Relators[i] == NULL) Mem_Error();
					p = *Relators[i + 20];
					q = *Relators[i];    
					while( (*q++ = *p++) ) ;
					}
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumRelators = 2;
				Find_Flow_A(NORMAL,1);
				if(Genus_Two_One_Relator_Annuli_And_Tori(FALSE,TRUE,TRUE) == 1) 
					{
if(H_Results != NULL) fprintf(H_Results,"toroidal.");
printf("\n\nL230");
Print_Relators(Relators,NumRelators);
					ReturnValue = 0;
					goto END;
					break;
					}
				}
			if(!BadR2)
				for(i = 1; i <= 2; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
					if(Relators[i] == NULL) Mem_Error();
					p = *Relators[i + 20];
					q = *Relators[i];    
					while( (*q++ = *p++) ) ;
					}
				Temp = Relators[1];	
				Relators[1] = Relators[2];
				Relators[2] = Temp;
				Length = GetHandleSize((char **) Relators[1]) - 1;
				NumRelators = 2;
				Find_Flow_A(NORMAL,1);
				if(Genus_Two_One_Relator_Annuli_And_Tori(FALSE,TRUE,TRUE) == 1)
					{
if(H_Results != NULL) fprintf(H_Results,"toroidal.");
printf("\n\nL256");
Print_Relators(Relators,NumRelators);					
					ReturnValue = 0;
					goto END;
					}
				ReturnValue = 1;
				goto END;
		case 1:
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			L1 = strlen((char*) ptr301);
			Relators[1] = (unsigned char **) NewHandle(L1 + 1);
			if(Relators[1] == NULL) Mem_Error();
			p = ptr301;
			q = *Relators[1];
			while( (*q++ = *p++) ) ;			
			for(i = 1; i <= 2; i++)
				{
				if(Relators[i + 1] != NULL) DisposeHandle((char **) Relators[i + 1]);
				Relators[i + 1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
				if(Relators[i + 1] == NULL) Mem_Error();
				p = *Relators[i + 20];
				q = *Relators[i + 1];    
				while( (*q++ = *p++) ) ;
				}
			NumRelators = 3;
			Length = L1;		
			Find_Flow_A(NORMAL,1);
printf("\n\nL283");
Print_Relators(Relators,NumRelators);
if(H_Results != NULL) fprintf(H_Results,"toroidal.");	
			NumRelators = 2;
			ReturnValue = 0;		
			break;
		case 2:
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			L2 = strlen((char*) ptr302);
			Relators[1] = (unsigned char **) NewHandle(L2 + 1);
			if(Relators[1] == NULL) Mem_Error();
			p = ptr302;
			q = *Relators[1];
			while( (*q++ = *p++) ) ;			
			for(i = 1; i <= 2; i++)
				{
				if(Relators[i + 1] != NULL) DisposeHandle((char **) Relators[i + 1]);
				Relators[i + 1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
				if(Relators[i + 1] == NULL) Mem_Error();
				p = *Relators[i + 20];
				q = *Relators[i + 1];    
				while( (*q++ = *p++) ) ;
				}
			NumRelators = 3;
			Length = L2;			
			Find_Flow_A(NORMAL,1);
printf("\n\nL308");
Print_Relators(Relators,NumRelators);
if(H_Results != NULL) fprintf(H_Results,"toroidal.");	
			NumRelators = 2;
			ReturnValue = 0;	
			break;
		case 3:
		case 4:
			if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
			L1 = strlen((char*) ptr301);
			Relators[1] = (unsigned char **) NewHandle(L1 + 1);
			if(Relators[1] == NULL) Mem_Error();
			p = ptr301;
			q = *Relators[1];
			while( (*q++ = *p++) ) ;
			if(Relators[2] != NULL) DisposeHandle((char **) Relators[2]);
			L2 = strlen((char*) ptr302);
			Relators[2] = (unsigned char **) NewHandle(L2 + 1);
			if(Relators[2] == NULL) Mem_Error();
			p = ptr302;
			q = *Relators[2];
			while( (*q++ = *p++) ) ;				
			for(i = 1; i <= 2; i++)
				{
				if(Relators[i + 2] != NULL) DisposeHandle((char **) Relators[i + 2]);
				Relators[i + 2] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i + 20])); 
				if(Relators[i + 2] == NULL) Mem_Error();
				p = *Relators[i + 20];
				q = *Relators[i + 2];    
				while( (*q++ = *p++) ) ;
				}
			NumRelators = 4;
			Length = L1 + L2;			
			Find_Flow_A(NORMAL,2);
printf("\n\nL341");
Print_Relators(Relators,NumRelators);
if(H_Results != NULL) fprintf(H_Results,"toroidal.");	
			NumRelators = 2;
			ReturnValue = 0;		
			break;
		default:
			ReturnValue = 1;
			goto END;
		}	
END:						
	if(ptr301 != NULL) DisposePtr((char *) ptr301);
	ptr301 = NULL;
	if(ptr302 != NULL) DisposePtr((char *) ptr302);
	ptr302 = NULL;		
	return(ReturnValue);                              
}

int Genus_Two_Meridian_Reps2_S3(int Flag)
{   								
    int           	i,
                    j,
                    LTRV = FALSE;
                                           
    unsigned int  	r;
    
    unsigned long   SLength;

    unsigned int   	Whitehead_Graph();
    
    if(NumGenerators != 2) return(11);
    if(NumRelators != 2)  return(12);
    
if(Flag == -1) goto _ALREADY_HAVE_DIAGRAM;    
    
    /*******************************************************************************************
        Call Find_Flow_A() to reduce Relators[1] U Relators[2] to minimal length before we 
        try to find the Heegaard diagram. Then call Whitehead_Graph() to actually find the 
        diagram. If Whitehead_Graph() doesn't return an error, then call Sep_Surface() to 
        check if H[Relators[1] U Relators[2]] is closed.
     ******************************************************************************************/
    
    SLength = Length;
    if(Flag > 0) 
    	{
    	printf("\n");
    	Micro_Print = TRUE;
    	}                         
    if(Find_Flow_A(NORMAL,FALSE))
    	{
    	if(Flag > 0) Micro_Print = FALSE;
		if(Length < SLength)
			{
			if(Length == 1)
				printf("\n R is primitive. Automorphism(s) reduced R to: ");
			else
				printf("\n R is a proper-power. Automorphism(s) reduced R to: ");
			printf("%s",(char *) *Relators[1]);
			}  	
    	return(1);
    	}
    if(Flag > 0) Micro_Print = FALSE;
    
    if(Length < SLength)
    	{
    	printf("\n The Relators did not have minimal length. Automorphism(s) reduced the Relators to: ");
    	Print_Relators(Relators,NumRelators);
    	}
    	    
_GET_DIAGRAM:
    
    Saved_Vertices = 0;
    TestRealizability1 = TRUE;
    r = Whitehead_Graph();     
    switch(r)
        {
        case NO_ERROR:
            break;
        case NON_PLANAR:
            printf("\n\n                    The Whitehead graph is nonplanar.");
            TestRealizability1 = FALSE;
            return(r);
        case FATAL_ERROR:
            printf("\n\nR is not realizable!");
            TestRealizability1 = FALSE;       
            return(r);
        case TOO_LONG:
            printf("\n\n                    This presentation may be too long!");
            TestRealizability1 = FALSE;
            return(r);
        case TOO_MANY_COMPONENTS:
        	TestRealizability1 = FALSE;
            return(r);        
        case NON_UNIQUE_1:
        case NON_UNIQUE_2:
        case NON_UNIQUE_3:
        case NON_UNIQUE_4:
         	printf("\n\nCan't find 'distinguished-slopes' unless H[R1 U R2] is uniquely determined by R1 U R2. Here R1 U R2 is: ");
        	Print_Relators(Relators,NumRelators);
        	TestRealizability1 = FALSE;
            return(r);
        case V2_ANNULUS_EXISTS:    
			printf("\n\nA V2_Annulus exists.");
			TestRealizability1 = FALSE;
			return(r);    
        case NOT_CONNECTED:
            printf("\n\n                    The Whitehead graph is not connected.");
            TestRealizability1 = FALSE;
            return(r);
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
                	printf("\n\nCan't find 'distinguished-slopes' unless H[R1 U R2] is uniquely determined by R1 U R2. Here R1 U R2 is: ");	
                	Print_Relators(Relators,NumRelators);
                	TestRealizability1 = FALSE;	
                    return(SEP_PAIRS);
                case 2: 
                	{
                	if(Micro_Print == 1)
                		printf("\n\nPerformed some level-transformations on the input presentation.");	   
                	goto _GET_DIAGRAM;
                	}
                default:
                	printf("\n\nCan't find 'distinguished-slopes' unless H[R1 U R2] is uniquely determined by R1 U R2. Here R1 U R2 is: ");       	
                	Print_Relators(Relators,NumRelators);
                	TestRealizability1 = FALSE;				
                    return(SEP_PAIRS);
                }    
        default:
        	printf("\n\nCan't find 'distinguished-slopes' unless H[R1 U R2] is uniquely determined by R1 U R2. Here R1 U R2 is: ");
        	Print_Relators(Relators,NumRelators);
        	TestRealizability1 = FALSE;
            return(r);
        }
    
    TestRealizability1 = FALSE; 
    
    if(LTRV == 2)
    	{
    	if(Flag != -1) printf("\n");
    	printf("\n Note: The Whitehead graph of R1 U R2 had a separating pair of vertices.");
    	printf("\n Performed some level-transformations on R1 U R2 to get R': ");
    	Print_Relators(Relators,NumRelators);
    	}
                                                    
    if(Sep_Surface() > 1) return(67);		/***** H[R] has two boundary components. *****/

_ALREADY_HAVE_DIAGRAM:
                                                                   
    /******************************************************************************************
            	We have found the Heegaard diagram, and H[R1 U R2] is closed. 
    ******************************************************************************************/
    
	if(Micro_Print == 1)
		{
		printf("\n\nThe current Presentation is:\n");
		Print_Relators(Relators,NumRelators);
		}

return(0);
}

int Init_Genus_Two_Meridian_Reps2_S1(int WRelator,char WDualRelator,char F1,unsigned long HS,unsigned long HS1,unsigned long HS2)
{
	char			i;
                   	
	int				Gap;
    						
	/** Determine if R1 <--> {A,a} and R2 <--> {B,b}, or R1 <--> {B,b} and R2 <--> {A,a} in the OutRelators[ ]. **/
	
	if(HS1 != HS2)
		{
		if(GetHandleSize((char **) OutRelators[1]) == GetHandleSize((char **) Relators[WRelator])) i = 'A';
		else i = 'B';
		}
		
	if(HS1 == HS2)
		{
		if(Compare_Str(*Relators[WRelator],*OutRelators[1],HS - 1)) i = 'A';
		else 
			{
			Inverse(*Relators[WRelator]);
			if(Compare_Str(*Relators[WRelator],*OutRelators[1],HS - 1)) i = 'A';
			else i = 'B';
			Inverse(*Relators[WRelator]);
			}
		}
	
	if(F1 == 0)	Gap = Genus_Two_Meridian_Reps2_S1(WDualRelator,i);	
	else 		Gap = Genus_Two_Meridian_Reps2_S2(i,F1);
	
	if(Gap > 0) Check_M1_and_M2_Primitivity(Gap);
	
	if(ToroidalR) printf("\n\nToroidalR = %d for Relator[%d] with Gap = %d.",ToroidalR,WRelator,Gap);
				
	return(Gap);		
}

int Genus_Two_Meridian_Reps2_S1(int F1,char F2)
{
    /*********************************************************************************************
        This routine is called by Genus_Two_Meridian_Reps2(). The routine tries to find a pair 
        of simple closed curves on the genus-two Heegaard surface that are disjoint from a wave 
        based at the non-positive relator indicated by F1. If successful, the routine returns 
        the words representing the disjoint curves in the strings ptr301 and ptr302.
    **********************************************************************************************/
    
    unsigned char  	*p,
                    *q,
                    *r;
                    
    int				Gap;
    
    unsigned int   	d,
    				e,
    				edge,
                    initial_e,
                    initial_v,
                    v,
                    vertex,
                    vv;
    
    unsigned long  	max;
    
    max = GetPtrSize((char *) ptr301) - 1;
           
    if(F2 == 'A') 
    	{
	   	p = (unsigned char *) strchr((char*) *DualRelators[F1],(int) 'A');
    	q = (unsigned char *) strchr((char*) *DualRelators[F1],(int) 'a');
    	if(p == NULL || q == NULL) return(1);
    	if(q < p)
    		{
    		r = p;
    		p = q;
    		q = r;    		
    		}	
    	}
     if(F2 == 'B') 
    	{
    	p = (unsigned char *) strchr((char*) *DualRelators[F1],(int) 'B');
    	q = (unsigned char *) strchr((char*) *DualRelators[F1],(int) 'b');
    	if(p == NULL || q == NULL) return(1);
    	if(q < p)
    		{
    		r = p;
    		p = q;
    		q = r;    		
    		}
    	}
    	
    /* Look for the last position r in DualRelators[F1] between p and q for which *r == *p. */
     	
    for(r = q - 1; r >= p; r--) if(*r == *p) break;
    	p = r;

    Gap = q - r - 1;
        
	e = p - *DualRelators[F1];
	edge = q - *DualRelators[F1];
		
	if(F1 == 1)
		{
		v = 0;
		vertex = 1;
		}
	else
		{
		v = 2;
		vertex = 3;
		}				
	edge = OSA[v] - edge;
	if(edge >= V[v]) edge -= V[v];
	initial_e = e;
	initial_v = v;	 
	r = ptr301;
	
	do
	  {
	  if(v & 1)
		  {
		  *r = (v >> 1) + 'a';
		  vv = v - 1;
		  }
	  else
		  {
		  *r = (v >> 1) + 'A';
		  vv = v + 1;
		  }
	  e = OSA[v] - e;
	  if(e >= V[v]) e -= V[v];
	  r++;
	  if(r - ptr301 > max )
		  {
		  r--;
		  *r = EOS;
		  return(-5001);
		  }
	  v = FV[vv];
	  d = A[vv][v];
	  while(d <= e)
		  {
		  v = CO[vv][v];
		  d += A[vv][v];
		  }
	  e = B[vv][v] - e;
	  }
	while(v != vertex || e != edge);
	
	/****** Freely reduce the string in ptr301. ******/

	r--;
	for(p = ptr301 + 1; abs(*p - *r) == 32 && p < r; p++, r--) ;
	r++;
	*r = EOS;
	
	/****** Move the freely reduced string in ptr301 so it starts at ptr301. *****/
			
	q = ptr301;
	while( (*q++ = *p++) ) ;
	
	/***** Set things up to find the second representative of the meridian. *****/
	
	e = edge;
	v = vertex;
	edge = initial_e;
	vertex = initial_v;				
	r = ptr302;

	do
		{
		if(v & 1)
		  {
		  *r = (v >> 1) + 'a';
		  vv = v - 1;
		  }
		else
		  {
		  *r = (v >> 1) + 'A';
		  vv = v + 1;
		  }
		e = OSA[v] - e;
		if(e >= V[v]) e -= V[v];
		r++;
		if(r - ptr302 > max)
		  {
		  r--;
		  *r = EOS;
		  return(-5001);
		  }
		v = FV[vv];
		d = A[vv][v];
		while(d <= e)
		  {
		  v = CO[vv][v];
		  d += A[vv][v];
		  }
		e = B[vv][v] - e;
		}
	while(v != vertex || e != edge);

	/****** Freely reduce the string in ptr302. ******/
	
	r--;
	for(p = ptr302 + 1; abs(*p - *r) == 32 && p < r; p++, r--) ;
	r++;
	*r = EOS;
	
	/****** Move the freely reduced string in ptr302 so it starts at ptr302. *****/
	
	q = ptr302;
	while( (*q++ = *p++) ) ;
	
	return(Gap);
}

int Genus_Two_Meridian_Reps2_S2(char F2,char F3)
{
    unsigned char  	*p,
                    *q,
                    *r;
                    
    int				Gap;
    
    unsigned int   	d,
    				e,
    				ee,
    				f,
    				edge,
                    m,
                    n,
                    v,
                    vertex,
                    vv;
    
    unsigned long  	max;
    
    max = GetPtrSize((char *) ptr301) - 1;
    
    /************************************************************************************  
		When the relator R indicated by F2 is positive, this routine will look for the 
		two nonseparating simple closed curves on the Heegaard surface disjoint from 
		R along with the 'horizontal' wave w to R.
    *************************************************************************************/
    
    if(F2 == 'A')
    	{
    	m = A[0][1] - 1;
    	p = *DualRelators[1];
    	for(q = p + m; q >= p; q--) if(*q == 'A' || *q == 'a') break;
    	ee = q - p;
    	}
    
    if(F2 == 'B')
    	{
    	m = A[0][1] - 1;
    	p = *DualRelators[1];
    	for(q = p + m; q >= p; q--) if(*q == 'B' || *q == 'b') break;
    	ee = q - p;
    	}
    
    if(F3 == 1)
    	{
    	if(F2 == 'A')
    		{
    		n = GetHandleSize((char **) DualRelators[2]) - 2;
 			p = *DualRelators[2];
    		for(q = p + n; q >= p; q--) if(*q == 'A' || *q == 'a') break;
    		f = q - p;   		
    		}
    	if(F2 == 'B')
   			{
    		n = GetHandleSize((char **) DualRelators[2]) - 2;
 			p = *DualRelators[2];
    		for(q = p + n; q >= p; q--) if(*q == 'B' || *q == 'b') break;
    		f = q - p;   		
    		}
    	Gap = m - ee + n - f;
    	if(CO[0][1] == 2) Gap += A[0][2];
    	else Gap += A[1][3];                   
    	}
    	
    if(F3 == 2)
    	{
    	if(F2 == 'A')
    		{
    		n = A[2][0];
    		if(CO[2][0] == 1) n += A[2][1];
 			p = *DualRelators[2];
    		for(q = p + n; *q; q++) if(*q == 'A' || *q == 'a') break;
    		f = q - p;   		
    		}
    	if(F2 == 'B')
   			{
    		n = A[2][0];
    		if(CO[2][0] == 1) n += A[2][1];
 			p = *DualRelators[2];
    		for(q = p + n; *q; q++) if(*q == 'B' || *q == 'b') break;
    		f = q - p;   		
    		}
    	Gap = m - ee + f - n;
    	if(CO[0][1] == 3) Gap += A[0][3];
    	else Gap += A[1][2];       	
    	}		

    e = ee;
    v = 0;    
    if(F3 == 1)
      	{
		vertex = 2;
		edge = f;
      	}    
    if(F3 == 2)
      	{
		vertex = 3;
		edge = B[2][3] - f;
      	}

	r = ptr301;	
	do
		{
		if(v & 1)
			{
			*r = (v >> 1) + 'a';
			vv = v - 1;
			}
		else
			{
			*r = (v >> 1) + 'A';
			vv = v + 1;
			}
		e = OSA[v] - e;
		if(e >= V[v]) e -= V[v];
		r++;
		if(r - ptr301 > max )
			{
			r--;
			*r = EOS;
			return(-5001);
			}
		v = FV[vv];
		d = A[vv][v];
		while(d <= e)
			{
			v = CO[vv][v];
			d += A[vv][v];
			}
		e = B[vv][v] - e;
	  }
	while(v != vertex || e != edge);	
	*r = EOS;
	
	/***** Set things up to find the second representative of the meridian. *****/

	edge = ee;
	vertex = 0;	
	if(F3 == 1)
		{
		v = 2;
		e = f;
		}	
	if(F3 == 2)
		{
		v = 3;
		e = B[2][3] - f;
		}

	r = ptr302;
		
	do
		{
		if(v & 1)
			{
			*r = (v >> 1) + 'a';
			vv = v - 1;
			}
		else
			{
			*r = (v >> 1) + 'A';
			vv = v + 1;
			}
		e = OSA[v] - e;
		if(e >= V[v]) e -= V[v];
		r++;
		if(r - ptr302 > max )
			{
			r--;
			*r = EOS;
			return(-5001);
			}
		v = FV[vv];
		d = A[vv][v];
		while(d <= e)
			{
			v = CO[vv][v];
			d += A[vv][v];
			}
		e = B[vv][v] - e;
	  }
	while(v != vertex || e != edge) ;	
	*r = EOS;
		
	return(Gap);	
}

int Check_Freely_Reduced_Dual_Presentation(void)
{
	unsigned char	*p,
					*q;
				
	int 			i;
	
	for(i = 1; i <= 2; i++)
		{
		p = q = *DualRelators[i];
		q++;
		while(1)
			{
			if(*q == EOS) 
				{
				q = *DualRelators[i];
				if(abs(*p - *q) == 32) return(1);
				return(0);
				}
			if(abs(*p - *q) == 32) return(1);
			p++;
			q++;			
			}		
		}
	return(0);	
}

int Check_M1_and_M2_Primitivity(int MyGap)
{
	char			M1Type,
					M2Type;
					
	unsigned char	*p,
					*q;
					
	unsigned long	L1,
					L2;					
	
	if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
	L1 = strlen((char*) ptr301);
	Relators[1] = (unsigned char **) NewHandle(L1 + 1);
	if(Relators[1] == NULL) Mem_Error();
	p = ptr301;
	q = *Relators[1];
	while( (*q++ = *p++) ) ;				
	M1Type = CheckPrimitivity();
	
	if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
	L2 = strlen((char*) ptr302);
	Relators[1] = (unsigned char **) NewHandle(L2 + 1);
	if(Relators[1] == NULL) Mem_Error();
	p = ptr302;
	q = *Relators[1];
	while( (*q++ = *p++) ) ;			
	M2Type = CheckPrimitivity();

	if(M1Type == -1 && MyGap == 1) ToroidalR = -5;		/* M1 is a proper-power but Gap == 1.	*/
	if(M1Type == -1 && MyGap >  1) ToroidalR = 1;		/* M1 is a proper-power and Gap >  1.	*/
	if(M2Type == -1 && MyGap == 1) ToroidalR = -6;		/* M2 is a proper-power but Gap == 1.	*/
	if(M2Type == -1 && MyGap >  1) ToroidalR = 2;		/* M2 is a proper-power and Gap >  1.	*/
	if(M1Type == -1 && M2Type == -1 && MyGap > 1) ToroidalR = 3;		/* Both M1 and M2 are proper-powers and Gap > 1.	*/
	if(L1 == L2 && M1Type && M1Type == M2Type) 
		{	
		if(Compare_Str(ptr301,ptr302,L1)) ToroidalR = 4; 		/* M1 and M2 are cyclic conjugates.		*/
		else
			{
			Inverse(ptr302);
			if(Compare_Str(ptr301,ptr302,L1)) ToroidalR = 4;	/* M1 and M2 inverse are cyclic conjugates.		*/
			Inverse(ptr302);	
			}	
		}
	
	/** Restore Relators[1]. **/
	
	if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
	Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[21]));
	if(Relators[1] == NULL) Mem_Error();
	p = *Relators[21];
	q = *Relators[1];
	while( (*q++ = *p++) ) ;
				
	return(0);
}