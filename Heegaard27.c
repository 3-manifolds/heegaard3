#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <string.h>
#include <ctype.h>

/****************************** Functions in Heegaard27.c ***********************************
L  17 ReRun_A_Bunch2(void)
L 232 ReRun_A_Bunch2_Sub1(int j)
L 342 ReRun_Batches_Of_Bunches2(void)
********************************************************************************************/

#define	INIT_NUM_FILLED 40000	/* Keep INIT_NUM_FILLED less than MAX_SAVED_PRES. */
#define MAX_W_FILLED 40000		/* Keep MAX_W_FILLED less than MAX_SAVED_PRES. */	

unsigned int NumPrimitivesFound;

int ReRun_A_Bunch2(void)
{
	/*************************************************************************************************
										The 1-X-1 'W' Option.
		Given a set S of presentations in 'Heegaard_Input_Presentations', all of which belong to one
		manifold M, this routine will search for HS Reps of M.								
		
		1) The presentations in S are saved in memory as presentations 40,000 . . . 40,000 + |S|.
		2) The saved presentations are fed to Stabilize(), which attempts to stabilize each saved 
		presentation. Distinct stabilized presentations are saved in memory as presentation 1, ....
		3) The stabilization process of step 2 is repeated 6*NumGenerators times, giving Heegaard an
		initial set S' of stabilized presentations to work with.
		4) Heegaard looks for additional new stabilized presentations, starting from members of S', 
		by using sequences of bandsums of relators to form new presentations.
		5) The set S'' of stabilized presentations, obtained in step 4, is saved in the file 
		'Heegaard_Input_Pres2'.
		6) Heegaard takes each relator R of each presentation P in S'' and checks if R is primitive. 
		If R is primitive, P is destabilized, and if the resulting destabilized presentation is new,
		it is saved in memory. This leaves an initial set of destabilized presentations S''' in
		memory.
		7) Heegaard looks for additional new destabilized presentations, starting from members of S''', 
		by using sequences of bandsums of relators to form new presentations.
		8) Finally, the augmented list of destabilized presentations, obtained in step 7, is processed, 
		grouped into equivalence classes and HS Reps found.													

		Note this routine does not do much error checking, as it assumes the input presentations 
		have already been run through Heegaard.

	**************************************************************************************************/
	
	FILE			*fptr1,
					*fptr2;
								
	unsigned char	*p,
					*q;
		
	int				i,
					j,
					k,
					NumStabTries,
					SNumFilled,
					SNumGenerators;
		
	Init_G_Variables();
	
	if((input_relators = fopen("Heegaard_Input_Presentations","r+")) == NULL)
        {
        printf("\n\nUnable to open the file 'Heegaard_Input_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        return(1);
        }
        
	printf("\n\nNOTE: This routine expects all the presentations in 'Heegaard_Input_Presentations'");
	printf("\nto belong to one manifold, and have equal numbers of generators.");
	printf("\n\nCONTINUE ? HIT 'y' OR 'n'.    ");
	GET_RESPONSE1:	
	switch(WaitkbHit())
		{
		case 'y':
			break;		
		case 'n':
			return(1);	
		default:
			goto GET_RESPONSE1;
		}	       
                    
    TotalComp = 1;
    CurrentComp = 1;
    NumFilled = INIT_NUM_FILLED;
    j = INIT_NUM_FILLED;   
	while(1)
		{
		if(Get_Next_Presentation_From_File(TRUE)) break;
		j++;
		if(ReRun_A_Bunch_Sub(FALSE,FALSE,j,0)) return(1);
		}
	SNumFilled = NumFilled;
	NumFilled = 0;
	NumStabTries = 6*NumGenerators;	
	if(NumFilled == 0) SNumGenerators = NumGenerators;
	if(NumGenerators != SNumGenerators)
		{
		printf("\n\nSomething is wrong here!");
		printf("\nThis routine expects all the presentations in 'Heegaard_Input_Presentations'");
		printf("\nto belong to one manifold, and have equal numbers of generators.");
		return(1);		
		}
	for(k = 1; k <= NumStabTries; k++)
		{
		for(j = INIT_NUM_FILLED; j < SNumFilled; j++)
			{
			NumGenerators = NG[j];
			NumRelators = NR[j];
			for(i = 1; i <= NumRelators; i++)
				{
				if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
				Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[j][i]));
				if(Relators[i] == NULL) Mem_Error();
				p = *SUR[j][i];
				q = *Relators[i];              
				while( (*q++ = *p++) ) ;
				}
			for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
			Length -= NumRelators;	    	
			if(Stabilize(FALSE)) continue;
			if(ReRun_A_Bunch_Sub(TRUE,FALSE,j+1,1)) return(1);
			if(NumFilled >= INIT_NUM_FILLED) break;
			}
		if(NumFilled >= INIT_NUM_FILLED) break;	
		}
 
	Check_If_HS_Rep					= FALSE;	
	Delete_Only_Short_Primitives 	= FALSE;	
	Do_Not_Reduce_Genus 			= TRUE;
	Find_All_Min_Pres 				= FALSE;
	FormBandsums 					= TRUE;
	OnlyReducingBandsums 			= FALSE;
				
	printf("\n\nHIT 'B' TO HAVE HEEGAARD LOOK FOR ADDITIONAL STABILIZED PRESENTATIONS USING BreadthFirstSearch.");
	printf("\nHIT 'D' TO HAVE HEEGAARD LOOK FOR ADDITIONAL STABILIZED PRESENTATIONS USING DepthFirstSearch.");
	printf("\nHIT 'Q' TO ABORT THIS RUN.    ");
	printf("\nNOTE: When satisfied, use the 'space-bar' to interrupt the search for additional stabilized presentations.");
	printf("\nThen hit 't' (if desired) to have Heegaard look for ways to destabilize the stabilized presentations.    ");
	GET_RESPONSE2:
	switch(WaitkbHit())
		{
		case 'B':
			BreadthFirstSearch	= TRUE;
			DepthFirstSearch	= FALSE;
			break;		
		case 'D':
			BreadthFirstSearch	= FALSE;
			DepthFirstSearch	= TRUE;
			break;
		case 'Q':
			return(1);		
		default:
			goto GET_RESPONSE2;
		}
	printf("\n\n");
	Input = RESET;
	if(Get_Diagrams() == INTERRUPT) return(0);	
	    
    fptr1 = input_relators;
    fptr2 = fopen("Heegaard_Input_Pres2","w+");  
	if(fptr2 == NULL)
        {
        printf("\n\nUnable to open the file 'Heegaard_Input_Pres2'.");
        return(1);
        }    
    input_relators = fptr2;          
        
    for(i = 0; i < NumFilled; i++)
    	{
    	fprintf(input_relators,"\n\nP %d) Gen %d, Rel %d, L %lu",i+1,NG[i],NR[i],SURL[i]);
    	Print_Relators3(SUR[i],NR[i]);
    	}
    	
    fseek(input_relators,0L,0);
    Delete_Old_Presentations();    
    NumPresExamined = 0;	
	Init_G_Variables();
	j = 0;
	while(1)
		{
		if(Get_Next_Presentation_From_File(FALSE)) break;
		j++;
		if(ReRun_A_Bunch2_Sub1(j) == 2) break;
		}
	Batch 				= FALSE;	
	FormBandsums 		= TRUE;
	BreadthFirstSearch 	= TRUE;
	DepthFirstSearch 	= FALSE;
	Input 				= RESET;
	for(i = 0; i < NumFilled; i++) 
		{
		HegSplNum[i] = i;
		HegSplNxt[i] = i;
		SURNumX[i]   = 1;
		NumLoops[i]  = 0;
		QPM[i] 		 = 0;
		UDV[i]		 = 0;
		}
	Mergers = 0;
	
	printf("\n\nHIT 'B' TO LOOK FOR ADDITIONAL DESTABILIZED PRESENTATIONS USING BreadthFirstSearch.");
	printf("\nHIT 'D' TO LOOK FOR ADDITIONAL DESTABILIZED PRESENTATIONS USING DepthFirstSearch.");
	printf("\nHIT 'Q' TO ABORT THIS RUN.    ");
	GET_RESPONSE3:
	switch(WaitkbHit())
		{
		case 'B':
			BreadthFirstSearch	= TRUE;
			DepthFirstSearch	= FALSE;
			break;		
		case 'D':
			BreadthFirstSearch	= FALSE;
			DepthFirstSearch	= TRUE;
			break;
		case 'Q':
			goto END;		
		default:
			goto GET_RESPONSE3;
		}
	printf("\n");			
	if(Get_Diagrams() == INTERRUPT) return(0);						
	Sort_Presentations_In_Memory(1);

END:
	input_relators = fptr1;
	fclose(fptr2);				  
	return(0);
}

int ReRun_A_Bunch2_Sub1(int j)
{
	unsigned char	**MyTemp,
					*p,
					*q,
					*r;

	int				i,
					jj,
					k,
					kk,
					NumEmptyRelators,
					SNumGenerators,
					SNumRelators;
									
	Freely_Reduce();	
	if(Rewrite_Input())
		{
		printf("\n\nHeegaard found an empty presentation.");
		return(1);
		}
	for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
	Length -= NumRelators;
	Vertices = 2*NumGenerators;
	Fill_A(NumRelators);
	Get_Matrix();
	if(Find_Flow_A(NORMAL,FALSE))
		{
		printf("\n\nAn error occurred in Find_Flow_A() at Presentation %u.",j);
		return(0);
		}
	for(i = 0; i < Vertices; i++) ZZ[i] = 0;
	if(Connected_(0,0) == FALSE)
		{
		printf("\n\nSkipped Presentation %u because its Whitehead graph is not connected.",j);
		return(0);
		}

	/* Stash this presentation.*/
	SNumRelators     = NumRelators;
	SNumGenerators   = NumGenerators;
	for(i = 1; i <= NumRelators; i++)
		{
		if(SMGP[1][i] != NULL) DisposeHandle((char **) SMGP[1][i]);
		SMGP[1][i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
		if(SMGP[1][i] == NULL) Mem_Error();
		p = *SMGP[1][i];
		r = *Relators[i];
		while( (*p++ = *r++) ) ;
		}
		
	for(i = 1; i <= SNumRelators; i++)
		{
		NumGenerators = SNumGenerators;
		Vertices = 2*NumGenerators;
		NumRelators = 1;
		if(Relators[1] != NULL) DisposeHandle((char **) Relators[1]);
		Relators[1] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[1][i]));
		if(Relators[1] == NULL) Mem_Error();
		p = *Relators[1];	
		q = *SMGP[1][i];
		while( (*p++ = *q++) ) ;		
		jj = CheckPrimitivity();
		NumRelators = SNumRelators;
		if(jj == 1)
			{
			for(k = 1; k <= NumRelators; k++)
				{
				if(Relators[k] != NULL) DisposeHandle((char **) Relators[k]);
				Relators[k] = (unsigned char **) NewHandle(GetHandleSize((char **) SMGP[1][k]));
				if(Relators[k] == NULL) Mem_Error();
				p = *Relators[k];
				r = *SMGP[1][k];
				while( (*p++ = *r++) ) ;			
				}
				
			if(i > 1)
				{
				MyTemp       = Relators[1];
				Relators[1]  = Relators[i];
				Relators[i]  = MyTemp;
				}
								
			kk = Find_Primitives(1);
			NumPrimitivesFound ++;
			if(kk != 1) continue;
			if(NumGenerators <= 1) continue;
			if(Defining_Relator_SPC() == TOO_LONG) continue;
			NumEmptyRelators = Freely_Reduce();
			if(NumEmptyRelators == TOO_LONG) continue;
			Rewrite_Input();
			if(NumGenerators <= 1) continue;
			if(NumRelators < 1) continue;
			for(k = 1,Length = 0; k <= NumRelators; k++) Length += GetHandleSize((char **) Relators[k]);
			Length -= NumRelators;
			kk = Find_Flow_A(NORMAL,FALSE);
			if(kk == TOO_LONG) continue;
			if(kk == 1) continue;
			Freely_Reduce();
			if(Length == 0) continue;
			CurrentComp = 1;
			if(On_File() < NumFilled) continue;
			if(NumFilled >= MAX_W_FILLED) return(2);
			Save_Pres(j-1,0,Length,1,6,0,0,0);					
			}
		}
		
	return(0);							
}

int ReRun_Batches_Of_Bunches2(void)
{
	/************************************************************************************************
									The Batch 'W' Option.
		This routine is essentially a version of the 1-X-1 'W' option which has a loop that allows it
		to process batches of bunches of presentations of different manifolds. (See 1-X-1 above for 
		some explanatory info.)
	*************************************************************************************************/

	FILE			*fptr1,
					*fptr2;
					
	char			EOFFlag,
					NumStabTries,
					StashedPres,					
					*SubName = " HS ";
	
	unsigned char	*CurrentPresName,
					*p,
					*q,
					*r,
					SBatch,
					SB10B11Finite,
					SB10B11HSReps,
					SB10B11Recognized,
					SB10B11SaveOnlyHS1P1,
					*StashedPresName;
										
	unsigned int	i,
					j,
					k,
					SMyMaxSavedPres,
					SNumFilled;
					
	long			SMyMaxNumDiagrams;				
					
	Init_G_Variables();
	
	if((input_relators = fopen("Heegaard_Input_Presentations","r+")) == NULL)
        {
        printf("\nUnable to open the file 'Heegaard_Input_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        return(1);
        }
 
 	if(H_Results != NULL) fclose(H_Results);
    H_Results = fopen("Heegaard_Results","a+");
	if(H_Results == NULL)
		{
        printf("\nUnable to open the file 'Heegaard_Results'.");
        return(1);		
		}	
	fprintf(H_Results,"Batch Option 'W', ");
			
	printf("\n\nHIT 'B' TO HAVE HEEGAARD SIMPLIFY USING BreadthFirstSearch.");
	printf("\nHIT 'D' TO HAVE HEEGAARD SIMPLIFY USING DepthFirstSearch.    ");
	GET_RESPONSE2:
	switch(WaitkbHit())
		{
		case 'B':
			BreadthFirstSearch		= TRUE;
			DepthFirstSearch		= FALSE;
			Batch = 11;
			break;		
		case 'D':
			BreadthFirstSearch		= FALSE;
			DepthFirstSearch		= TRUE;
			Batch = 10;
			break;	
		default:
			goto GET_RESPONSE2;
		}
	printf("\n");
	if(BreadthFirstSearch)
		fprintf(H_Results,"BreadthFirstSearch = TRUE, Stabilized 1X, ");
	if(DepthFirstSearch)
		fprintf(H_Results,"DepthFirstSearch = TRUE, Stabilized 1X, ");

	SetLimits();
	SMyMaxNumDiagrams 	= MyMaxNumDiagrams;
	SMyMaxSavedPres 	= MyMaxSavedPres;
	
	SB10B11Finite 			= FALSE;
	SB10B11Recognized 		= FALSE;
	SB10B11HSReps			= TRUE;
	SB10B11SaveOnlyHS1P1	= 1;
	
	NumPresExamined = 0;
         	
	/*** Process bunches of presentations. ***/
		
	fseek(input_relators,0L,0);
	StashedPres 		= FALSE;
	StashedPresName		= (unsigned char *)  NewPtr(MAXLENGTH + 1);
	if(StashedPresName 	== NULL) Mem_Error();
	CurrentPresName		= (unsigned char *)  NewPtr(1003);
	if(CurrentPresName 	== NULL) Mem_Error();	
	p = CurrentPresName;
	*p++ = '#';
	*p++ = '$';
	*p++ = '@';
	*p++ = '&';
	*p = EOS;
	SBatch = Batch;
	EOFFlag = FALSE;
		
	while(1)
		{
		Delete_Old_Presentations();
		Init_G_Variables();
		Check_If_HS_Rep 				= FALSE;
		B10B11Recognized				= SB10B11Recognized;
		B10B11Finite					= SB10B11Finite;
		B10B11HSReps					= SB10B11HSReps;
		B10B11SaveOnlyHS1P1				= SB10B11SaveOnlyHS1P1;	
		TotalComp = 1;	
    	CurrentComp = 1;
    	NumFilled = INIT_NUM_FILLED;
    	printf("\n------------------------------------");
		while(1)
			{							   
			/****************************************************
				Try to load the next bunch of presentations.
			****************************************************/
							
			if(StashedPres) /*** Load the stashed presentation as Presentation 1. ***/
				{
				p = PresName;
				r = StashedPresName;
				while( (*p++ = *r++) ) ;
				q = (unsigned char *) strstr((char *) PresName,SubName);
				if(q == NULL) 
					{
					/* Don't want to process presentations that aren't HS Reps. */
					printf("\n\nThis routine expects Presentation names to contain ' HS d', where d is a digit!");
					printf("\nBad Name: %s",PresName);
					goto END; 
					}
				if(!isdigit(*(q + 4))) 
					{
					/* Don't want to process presentations that aren't HS Reps. */
					printf("\n\nThis routine expects Presentation names to contain ' HS d', where d is a digit!");
					printf("\nBad Name: %s",PresName);
					goto END; 
					}	
				p = PresName;
				r = CurrentPresName;
				if(q - p > 1000) 
					{
					/* The NewPresName will be too long! */
					printf("\n\nStopping because a presentation's name is too long!");
					printf("\nBad Name: %s",PresName);
					*q = EOS;
					goto END; 
					}	
				*q = EOS;
				while( (*r++ = *p++) ) ;					
				StashedPres = FALSE;
				j = INIT_NUM_FILLED;
				NumRelators		= CopyNumRelators;
				NumGenerators 	= CopyNumGenerators;
				Vertices 		= 2*NumGenerators;
				for(i = 1; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Input[i]));
					if(Relators[i] == NULL) Mem_Error();              
					p = *Copy_Of_Input[i];
					q = *Relators[i];
					while( (*q++ = *p++) ) ;
					}				
				if(ReRun_A_Bunch_Sub(FALSE,FALSE,j,0)) break;
				}
			if(EOFFlag) goto END;	
			if(Get_Next_Presentation_From_File(FALSE)) 
				{
				if(NumFilled) 
					{
					EOFFlag = TRUE;
					p = PresName;
					r = CurrentPresName;
					while( (*p++ = *r++) ) ;					
					break;
					}
				else goto END;
				}
			q = (unsigned char *) strstr((char *) PresName,SubName);
			if(q == NULL)
				{
				/* Don't want to process presentations that aren't HS Reps. */
				printf("\n\nThis routine expects Presentation names to contain ' HS d', where d is a digit!");
				printf("\nBad Name: %s",PresName);				
				goto END; 
				}
			if(!isdigit(*(q + 4)))
				{
				/* Don't want to process presentations that aren't HS Reps. */
				printf("\n\nThis routine expects Presentation names to contain ' HS d', where d is a digit!");
				printf("\nBad Name: %s",PresName);
				goto END; 
				}	
			r = (unsigned char *) strstr((char *) PresName,(char *) CurrentPresName);
			if(r == NULL || r >= q) /* Found the first presentation of a new bunch. */
				{
				if(NumFilled == INIT_NUM_FILLED) /* Save this presentation. Update CurrentPresName. */
					{
					p = PresName;
					r = CurrentPresName;
					q = (unsigned char *) strstr((char *) PresName,SubName);
					if(q - p > 1000) 
						{
						/* The NewPresName will be too long! */
						printf("\n\nStopping because a presentation's name is too long!");
						printf("\nBad Name: %s",PresName);
						goto END; 
						}	
					*q = EOS;
					while( (*r++ = *p++) ) ;				
					j = INIT_NUM_FILLED;
					if(ReRun_A_Bunch_Sub(FALSE,FALSE,j,0)) goto END;
					}
				else
					{ 
					/* Stash this presentation.*/
					CopyNumRelators     = NumRelators;
					CopyNumGenerators   = NumGenerators;
					for(i = 1; i <= NumRelators; i++)
						{
						if(Copy_Of_Input[i] != NULL) DisposeHandle((char **) Copy_Of_Input[i]);
						Copy_Of_Input[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
						if(Copy_Of_Input[i] == NULL) Mem_Error();
						p = *Copy_Of_Input[i];
						r = *Relators[i];
						while( (*p++ = *r++) ) ;
						}
					p = PresName;
					r = StashedPresName;
					while( (*r++ = *p++) ) ;
					StashedPres = TRUE;	
					p = PresName;
					r = CurrentPresName;					
					while( (*p++ = *r++) ) ;
					break;					
					}	
				}
			else
				{
				/* 	The presentation retrieved from 'Heegaard_Input_Presentations' belongs to the current bunch. Save it.*/
				j ++;
				if(ReRun_A_Bunch_Sub(FALSE,FALSE,j,0)) goto END;
				}	
			}
		SNumFilled = NumFilled;	
		/* Stabilize the input presentations. */
		NumFilled = 0;
		NumStabTries = 6*NumGenerators;
		for(k = 1; k <= NumStabTries; k++)
			{
			for(j = INIT_NUM_FILLED; j < SNumFilled; j++)
				{
				NumGenerators = NG[j];
				NumRelators = NR[j];
				for(i = 1; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[j][i]));
					if(Relators[i] == NULL) Mem_Error();
					p = *SUR[j][i];
					q = *Relators[i];              
					while( (*q++ = *p++) ) ;
					}
				for(i = 1,Length = 0; i <= NumRelators; i++) Length += GetHandleSize((char **) Relators[i]);
				Length -= NumRelators;	    	
				if(Stabilize(FALSE)) continue;
				if(ReRun_A_Bunch_Sub(TRUE,FALSE,j+1,1)) return(1);
				if(NumFilled >= INIT_NUM_FILLED) break;
				}
			if(NumFilled >= INIT_NUM_FILLED) break;	
			}		
			
		printf("\n\nProcessing %s. Hit 's' or ' ' for status reports.",PresName);
		
		MyMaxSavedPres					= SMyMaxSavedPres;
		MyMaxNumDiagrams				= SMyMaxNumDiagrams;	
		Delete_Only_Short_Primitives 	= FALSE;
		Do_Not_Reduce_Genus 			= TRUE;
		Find_All_Min_Pres				= FALSE;
		FormBandsums 					= TRUE;
		OnlyReducingBandsums 			= FALSE;
		NumPresExamined ++;
		Batch = SBatch;
		Input = RESET;
		
		for(i = 0; i < NumFilled; i++) 
			{
			HegSplNum[i] = i;
			HegSplNxt[i] = i;
			SURNumX[i]	 = 1;
			NumLoops[i]  = 0;
			QPM[i] 		 = 0;
			UDV[i]		 = 0;
			}
		Mergers = 0;
		
		if(Get_Diagrams() == INTERRUPT) goto END;
		SNumFilled = NumFilled;
		fptr1 = input_relators;
		fptr2 = fopen("Heegaard_Input_Pres2","w+");  
		if(fptr2 == NULL)
			{
			printf("\n\nUnable to open the file 'Heegaard_Input_Pres2'.");
			return(1);
			}    
		input_relators = fptr2;          
		
		for(i = 0; i < NumFilled; i++)
			{
			fprintf(input_relators,"\n\n%s HS %d, Gen %d, Rel %d, L %lu",CurrentPresName,i+1,NG[i],NR[i],SURL[i]);
			Print_Relators3(SUR[i],NR[i]);
			}
		
		/****************************************************************
			Call ReRun_A_Bunch2_Sub1() to delete all primitives from the
			stabilized presentations saved in 'Heegaard_Input_Pres2'.	
		*****************************************************************/
		fseek(input_relators,0L,0);
		Delete_Old_Presentations();	
		Init_G_Variables();
		NumPrimitivesFound = 0;
		j = 0;
		while(1)
			{
			if(Get_Next_Presentation_From_File(FALSE)) break;
			j++;
			if(ReRun_A_Bunch2_Sub1(j) == 2) break;
			}

		for(i = 0; i < NumFilled; i++) 
			{
			HegSplNum[i] = i;
			HegSplNxt[i] = i;
			SURNumX[i]	 = 1;
			NumLoops[i]  = 0;
			QPM[i] 		 = 0;
			UDV[i]		 = 0;
			}
		Mergers = 0;
					
		MyMaxSavedPres 					= MY_MAX_SAVED_PRES_2;
		MyMaxNumDiagrams				= MY_MAX_NUM_DIAGRAMS;
		Delete_Only_Short_Primitives 	= FALSE;
		Do_Not_Reduce_Genus 			= TRUE;
		Find_All_Min_Pres				= FALSE;
		FormBandsums 					= TRUE;
		OnlyReducingBandsums 			= FALSE;
		Batch = SBatch;	
		Input = RESET;
		printf("\n\nHeegaard derived %u distinct destabilized presentations from %u primitives in %u presentations.",
			NumFilled,NumPrimitivesFound,SNumFilled);
		printf("\n\nLooking for additional destabilized presentations. . .");		
		if(Get_Diagrams() == INTERRUPT) goto END;
		p = PresName;
		r = CurrentPresName;					
		while( (*p++ = *r++) ) ;								
		Sort_Presentations_In_Memory(1);
		input_relators = fptr1;
		fclose(fptr2);		
		if(EOFFlag) goto END;
		}
END:
	if(StashedPresName != NULL) DisposePtr((unsigned char *) StashedPresName);
	if(CurrentPresName != NULL) DisposePtr((unsigned char *) CurrentPresName);
	input_relators = fptr1;
	fclose(fptr2);
			
	return(0);
}