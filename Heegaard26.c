#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <string.h>
#include <ctype.h>

/****************************** Functions in Heegaard26.c ***********************************
L  11 ReRun_Batches_Of_Bunches(void)
L 362 Set_Up_Simplification_Parameters_S2(void)
********************************************************************************************/

int ReRun_Batches_Of_Bunches(void)
{
	/************************************************************************************************
									The Batch 'T' Option.
		This routine will rerun all of the presentations in the file 'Heegaard_Input_Presentations'
		in bunches. A set of consecutive presentations in 'Heegaard_Input_Presentations' forms a 
		'bunch' if each presentation's name begins with a string of the form 'xxxxxx HS ' followed 
		by at least one digit.
		Options:
			1) Append stabilized versions of each input presentations to the set of initial
			presentations.
			2) Look for manifolds with finite π1, other recognizable presentations, and/or HS Reps
			of the input presentations.
		Results are printed to 'Heegaard_Results'.		
		The user can set limits on the number of presentations Heegaard saves before moving on, and
		may also set limits on the number of diagrams Heegaard examines before moving on.
			Note this routine does not do much error checking, as it assumes incoming presentations
		have been previously run through Heegaard.				
	*************************************************************************************************/
		
	char			EOFFlag,
					NumStabs,
					NumStabTries,
					StabilizeInputs,
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
					SNumFilled;
					
	Init_G_Variables();
	
	if((input_relators = fopen("Heegaard_Input_Presentations","r+")) == NULL)
        {
        printf("\nUnable to open the file 'Heegaard_Input_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        return(1);
        }
 
 	if(H_Results != NULL) 
		{
		fclose(H_Results);
		H_Results = NULL;
		}
    H_Results = fopen("Heegaard_Results","a+");
	if(H_Results == NULL)
		{
        printf("\nUnable to open the file 'Heegaard_Results'.");
        return(1);		
		}
	fprintf(H_Results,"Batch Option 'T', ");
		
 	printf("\n\nSTABILIZE EACH INPUT PRESENTATION? HIT 'y' OR 'n'    ");
	GET_RESPONSE1:
	switch(WaitkbHit())
		{
		case 'y':
			StabilizeInputs		= TRUE;
			SNumFilled = NumFilled;
			break;		
		case 'n':
			StabilizeInputs		= FALSE;
			break;	
		default:
			goto GET_RESPONSE1;
		}
	
	if(StabilizeInputs) 
		{
		printf("\n\nINCREASE GENUS BY? HIT '0', '1', '2', '3', '4' OR '5'	");
		GET_RESPONSE3:
		NumStabs = WaitkbHit();
		if(NumStabs < 48 || NumStabs > 53) goto GET_RESPONSE3;
		NumStabs -= 48;
		if(NumStabs == 0) StabilizeInputs = FALSE;
		}
		
	if(StabilizeInputs && NumStabs == 1)
		{
		printf("\nSTABILIZE EACH PRESENTATION UP TO N DISTINCT WAYS? Choose '1' - '9' for N.    ");
		GET_RESPONSE4:
		NumStabTries = WaitkbHit();
		if(NumStabTries < 49 || NumStabTries > 57) goto GET_RESPONSE4;
		NumStabTries -= 48;
		}
	if(NumStabs > 1) NumStabTries = 1;			

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
	
	if(BreadthFirstSearch && H_Results != NULL)
		fprintf(H_Results,"BreadthFirstSearch = TRUE, Stabilized %dX, ",NumStabs);
	if(DepthFirstSearch && H_Results != NULL)
		fprintf(H_Results,"DepthFirstSearch = TRUE, Stabilized %dX, ",NumStabs);

	Set_Up_Simplification_Parameters_S2();
	SB10B11Finite 			= B10B11Finite;
	SB10B11Recognized 		= B10B11Recognized;
	SB10B11HSReps			= B10B11HSReps;
	SB10B11SaveOnlyHS1P1	= B10B11SaveOnlyHS1P1;
         	
	/*** Process bunches of presentations. ***/
		
	fseek(input_relators,0L,0);
	StashedPres 		= FALSE;
	StashedPresName		= (unsigned char *) NewPtr(MAXLENGTH + 1);
	if(StashedPresName 	== NULL) Mem_Error();
	CurrentPresName		= (unsigned char *) NewPtr(1003);
	if(CurrentPresName 	== NULL) Mem_Error();	
	p = CurrentPresName;
	*p++ = '#';
	*p++ = '$';
	*p++ = '@';
	*p++ = '&';
	*p = EOS;
	SBatch = Batch;
	EOFFlag = FALSE;
	NumPresExamined = 0;
		
	while(1)
		{
		Delete_Old_Presentations();
		Init_G_Variables();
		Delete_Only_Short_Primitives 	= FALSE;
		Do_Not_Reduce_Genus 			= FALSE;
		FormBandsums 					= TRUE;
		OnlyReducingBandsums 			= FALSE;
		B10B11Recognized				= SB10B11Recognized;
		B10B11Finite					= SB10B11Finite;
		B10B11HSReps					= SB10B11HSReps;
		B10B11SaveOnlyHS1P1				= SB10B11SaveOnlyHS1P1;		
    	CurrentComp = 1;
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
				j = 1;
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
				if(NumFilled == 0) /* Save this presentation. Update CurrentPresName. */
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
					j = 1;
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
				/* 	The presentation retreived from 'Heegaard_Input_Presentations' belongs to the current bunch. Save it.*/
				j ++;
				if(ReRun_A_Bunch_Sub(FALSE,FALSE,j,0)) goto END;
				}	
			}
		SNumFilled = NumFilled;	
		if(StabilizeInputs) for(j = 0; j < SNumFilled; j++) 
			{
			for(k = 1; k <= NumStabTries; k++)
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
				for(i = 0; i < NumStabs; i++) if(Stabilize(FALSE)) break;
				if(i < NumStabs) continue;
				if(ReRun_A_Bunch_Sub(TRUE,FALSE,j+1,NumStabs)) goto END;			
				}
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
		Mergers = 0;				
		printf("\n\nProcessing %s. Hit 's' or ' ' for status reports.",PresName);		
		Input = RESET;
		Batch = SBatch;
		NumPresExamined ++;
		if(Get_Diagrams() == INTERRUPT) goto END;						
		Sort_Presentations_In_Memory(1);		
		if(EOFFlag) goto END;
		}
END:
	if(StashedPresName != NULL) DisposePtr((unsigned char *) StashedPresName);
	if(CurrentPresName != NULL) DisposePtr((unsigned char *) CurrentPresName);
	if(H_Results != NULL) 
		{
		fflush(H_Results);
		fclose(H_Results);
		H_Results = NULL;
		}	
	return(0);
}

int Set_Up_Simplification_Parameters_S2(void)
{
	printf("\nSELECT ONE OF THE FOLLOWING:");
	printf("\n1) Save info about each recognized manifold.");
	printf("\n2) Save info about each finite manifold.");
	printf("\n3) Save info about HS Reps.");
	printf("\n\n1) SAVE INFO ABOUT EACH RECOGNIZED MANIFOLD TO 'Heegaard_Results' ? HIT 'y' OR 'n'.    ");
	GET_RESPONSE1:       
	switch(WaitkbHit())
		{
		case 'y':
			B10B11Recognized 	= TRUE;
			fprintf(H_Results,"General recognition = TRUE, ");
			B10B11Finite 		= FALSE;			                
			break;		
		case 'n':
			B10B11Recognized 	= FALSE;
			B10B11Finite		= FALSE;   
			break;        				
		default:
			SysBeep(5);
			goto GET_RESPONSE1;    
		}	

	if(B10B11Recognized == FALSE)
		{
		printf("\n\n2) SAVE INFO ABOUT EACH FINITE MANIFOLD TO 'Heegaard_Results' ? HIT 'y' OR 'n'.    ");	
		GET_RESPONSE2:       
		switch(WaitkbHit())
			{
			case 'n':
				B10B11Finite	= FALSE;
				fprintf(H_Results,"Both General and Finite recognition = FALSE, ");  
				break;        
			case 'y':
				B10B11Finite 	= TRUE;
				fprintf(H_Results,"Finite recognition = TRUE, ");			                
				break;				
			default:
				SysBeep(5);
				goto GET_RESPONSE2;    
			}
		}	
	
	if(!B10B11Finite && !B10B11Recognized)
		{
		printf("\n\n3) SAVE INFO ABOUT HS REPS FOUND TO 'Heegaard_Results' ? HIT 'y' OR 'n'.    ");
		GET_RESPONSE3:       
		switch(WaitkbHit())
			{
			case 'n':
				B10B11HSReps	= FALSE;
				fprintf(H_Results,"Saving HS Rep Info = FALSE, ");  
				break;        
			case 'y':
				B10B11HSReps 	= TRUE;			                
				break;				
			default:
				SysBeep(5);
				goto GET_RESPONSE3;    
			}	
	
		if(B10B11HSReps == TRUE)
			{
			printf("\n    HIT 1 TO SAVE ALL HS REPS FOUND TO 'Heegaard_Results'.  ");
			printf("\n    HIT 2 TO SAVE ONLY HS 1, P 1 TO 'Heegaard_Results'.  ");
			printf("\n    HIT 3 TO SAVE ALL TUNNELS OF JUST TUNNEL-NUMBER-ONE MANIFOLDS TO 'Heegaard_Results'.  ");
			printf("\n    HIT 4 TO SAVE ONLY TUNNELS OF TUNNEL-NUMBER-ONE MANIFOLDS WITH ONE TUNNEL TO 'Heegaard_Results'.    ");
			GET_RESPONSE4:
			switch(WaitkbHit())
				{
				case '1':
					B10B11SaveOnlyHS1P1	= 1;
					fprintf(H_Results,"Save all HS Reps = TRUE, "); 
					break;        
				case '2':
					B10B11SaveOnlyHS1P1 = 2;	
					fprintf(H_Results,"SaveOnlyHS1P1 = TRUE, ");		                
					break;
				case '3':
					B10B11SaveOnlyHS1P1 = 3;	
					fprintf(H_Results,"SaveAllTunnelsOfJustTunnelNumberOneManifolds = TRUE, ");		                
					break;
				case '4':
					B10B11SaveOnlyHS1P1 = 4;	
					fprintf(H_Results,"SaveOnlyTunnelsOfTunnelNumberOneManifoldsWithOneTunnel = TRUE, ");		                
					break;														
				default:
					SysBeep(5);
					goto GET_RESPONSE4;    
				}
			}
		}

	SetLimits();  
         	
    return(0);	   
}
