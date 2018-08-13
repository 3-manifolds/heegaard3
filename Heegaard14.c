#include "Heegaard.h"
#include "Heegaard_Dec.h"
#include <ctype.h>

/****************************** Functions in Heegaard14.c **********************************
L   15 BatchProcessing(void)
L 1507 Get_Min_Length_Parameter(void)
L 1124 Set_Up_Simplification_Parameters(int* SFormBandsums, int* SOnlyReducingBandsums,
	   int* SDelete_Only_Short_Primitives, int* SDo_Not_Reduce_Genus)
L 1243 Set_Up_Simplification_Parameters_S1(void)
L 1367 SetLimits(void)
L 1413 SnapPy2Heegaard(void)
********************************************************************************************/

int BatchProcessing(void)
{
	char			WKBHRV;
	
	unsigned char 	*p,
                   	*q,
                   	Stop,
                   	**Temp;
      
    int	   			I,
    				Min_Length_Parameter,
    				SDelete_Only_Short_Primitives,
    				SDo_Not_Reduce_Genus,
    				SFormBandsums,
    				SOnlyReducingBandsums,
    				SMicro_Print_F,
    				TargetNumGenerators;  
                            
    unsigned int    BNumEmpty,
    				BNumIndeterminate,
    				BNumTooLong,
    				i,
    				Sum;
    
    long            Scratch;
 
OPTIONS:  
	H_Results = H_Results_2 = NULL;
	MyMaxNumDiagrams = MY_MAX_NUM_DIAGRAMS;
	  
    if((input_relators = fopen("Heegaard_Input_Presentations","r+")) == NULL)
        {
        SysBeep(5);
        printf("\nUnable to open the file 'Heegaard_Input_Presentations'.");
        printf("\nPlease locate the file 'Heegaard_Input_Presentations', make sure it is closed,");
        printf("\nand place it in the parent folder of the folder containing Heegaard.");
        return(1);
        }
    
    /**************************************************************************************
							Present the user with some options.
	**************************************************************************************/

printf("\nSOME OPTIONS:\n");

printf("\nTWO-GENERATOR OPTIONS:");
	printf("\n	Hit 'a' TO COMPUTE ALEXANDER POLYNOMIALS OF 2-GENERATOR, 1-RELATOR PRESENTATIONS.");
	printf("\n	HIT 'b' TO FIND 'distinguished-slope' REPS M1 & M2 OF H[R]. (E.g. to check if R is a knot relator.)");
	printf("\n	Note: 'Distinguished-slope' reps depend only on the relator R.");
	printf("\n	HIT 'c' TO HAVE HEEGAARD CHECK IF H[R] IS ANANULAR OR ATOROIDAL.");
	printf("\n	HIT 'f' TO HAVE HEEGAARD CHECK IF H[R] IS FIBERED.");
	printf("\n	HIT 'p' TO HAVE HEEGAARD CHECK IF R IS POSITIVE. (If R is non-positive, the only cyclic or reducing"); 
	printf("\n	filling of H[R] is at the 'distinguished-slope'.)");
	printf("\n	HIT 'E' TO HAVE HEEGAARD CHECK FOR 'UNIVERSAL MINIMIZING' MERIDIONAL DISKS IN H.");	
printf("\nVARIOUS INITIAL PRESENTATION CHECKS:");
	printf("\n	HIT 'C' TO CHECK IF THE INITIAL PRESENTATION IS A \042HS REP\042. (Heegaard will alert the user if a");  
	printf("\n	sequence of handle-slides of the initial presentation P yields a presentation P' with |P'| < |P|.)");
	printf("\n	HIT 'd' TO SEE DATA FOR HEEGAARD DIAGRAMS OF PRESENTATIONS.");
	printf("\n	HIT 'D' TO SEE THE DUAL RELATORS OF EACH REALIZABLE PRESENTATION'S DIAGRAM.");
	printf("\n	HIT 'g' TO CHECK REALIZABILITY OF PRESENTATIONS.");
	printf("\n	HIT 'h' TO FIND THE INTEGRAL FIRST HOMOLOGY OF PRESENTATIONS.");
	printf("\n	HIT 'l' TO FIND |LTs|, |Orbit|, |WoSepVert| AND |PseudoMin| UNDER LEVEL TRANSFORMATIONS.");
	printf("\n	HIT 'L' TO LOOK FOR NON-MINIMAL, UNSTABILIZED SPLITTINGS.");
	printf("\n	HIT 'm' TO CHECK MANIFOLDS FOR PSEUDO-MINIMALITY.");
	printf("\n	HIT 's' TO FIND SYMMETRIES OF PRESENTATIONS.");	      
printf("\nPRESENTATION MODIFICATION ROUTINES:");
	printf("\n	HIT 'u' TO STABILIZE PRESENTATIONS WHILE PRESERVING REALIZABILITY.");
printf("\nPRESENTATION SIMPLIFICATION ROUTINES:");
	printf("\n	HIT 'r' TO REDUCE AND SIMPLIFY PRESENTATIONS USING DEPTH-FIRST SEARCH AND SEP_VERT SLIDES.");
	printf("\n	HIT 'R' TO REDUCE AND SIMPLIFY PRESENTATIONS USING BREADTH-FIRST SEARCH AND SEP_VERT SLIDES.");
	printf("\n	HIT 'x' TO SIMPLIFY PRESENTATIONS BY SUCCESSIVELY DELETING PRIMITIVES, WITHOUT CHECKING REALIZABILITY.");
	printf("\n	HIT 'X' TO FIND PRESENTATIONS OBTAINED BY DELETING PRIMITIVES FROM ONLY INITIAL PRESENTATIONS.");
	printf("\n	HIT 'z' TO REDUCE PRESENTATIONS TO MINIMAL LENGTH.");      
printf("\nMISCELLANEOUS OPTIONS:");
	printf("\n	HIT 'q' TO QUIT RUNNING IN BATCH MODE.");		
	printf("\n	HIT 'S' TO CONVERT SNAPPY FORMAT PRESENTATIONS TO HEEGAARD READABLE PRESENTATIONS.");
	printf("\n	HIT 'T' TO STABILIZE AND RERUN BATCHES OF BUNCHES OF HS REPS FROM MULTIPLE MANIFOLDS.");
	printf("\n	HIT 'U' TO HAVE HEEGAARD STABILIZE THE IP, COMPUTE HS REPS AND CHECK IF THE IP APPEARS ON THE HS LIST.");
	printf("\n	HIT 'W' TO LOOK FOR HS REPS FOR THE ENTIRE SET OF PRESENTATIONS IN 'Heegaard_Input_Presentations'.");
	printf("\n	HIT 'Z' TO FIND PRIMITIVES, PROPER_POWERS, OR CURVES WITH LESS THAN FULL RANK DISJOINT FROM RELATORS.    ");
	
GET_RESPONSE3: 
	WKBHRV = WaitkbHit();
	printf("\n");      
	switch(WKBHRV)
		{
		case 'a':
			Batch = 1;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'a' ");
				fprintf(H_Results,"\n\nAlexander polynomials of each 1-relator, 2-generator presentation should appear below.");
				}
			break;
			         	
		case 'b':
			Batch = 2;
			printf("\n\n	Note: If simplifying < A,B | R1,M1,M2 > yields S^3, R1 is a knot relator.");
			printf("\n  If Heegaard produces a pseudo-minimal PM diagram != S^3, R1 is not a knot relator."); 
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'b' ");
				fprintf(H_Results,"\n\nEach uniquely realizable 2-gen initial relator R1 and its two canonical 'distinguished-slope' reps M1 and M2 should appear below. "); 
				fprintf(H_Results,"Note M1 and M2 are completely determined by the Heegaard diagram realizing R1. ALso note: ");
				fprintf(H_Results,"Running these presentations and simplifying will yield S^3 iff H[R1] is the exterior of a tunnel number one knot.");
				}  			
			break;
			
		case 'C':
			Batch = 4;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'C' ");
				fprintf(H_Results,"\n\nIndication that a presentation is a 'Heegaard Splitting Rep' should appear below.");	
				}		
			SetLimits();     
			break;
		
		case 'c':
			Batch = 56;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'c' ");
				fprintf(H_Results,"\n\nWhether a 1-relator, 2-generator manifold H[R] is annular or toroidal should appear below.");	
				}
			break;
									   
		case 'd':
			Batch = 5;
			printf("\n\nSHOW WHICH FACES OF EACH DIAGRAM FORM BDRY COMPONENTS ?  HIT 'y' OR 'n'.    ");
			GET_B5RESPONSE1:
			switch(WaitkbHit())
				{
				case 'y':
					B5PrintBdryComps = TRUE;
					break;
				case 'n':
					B5PrintBdryComps = FALSE;
					break;
				default:
					SysBeep(5);
					goto GET_B5RESPONSE1;
				}
			printf("\n\nPRINT DUAL RELATORS OF EACH DIAGRAM ? HIT 'y' OR 'n'.    ");
			GET_B5RESPONSE2:
			switch(WaitkbHit())
				{
				case 'y':
					B5PrintDualRelators = TRUE;
					break;
				case 'n':
					B5PrintDualRelators = FALSE;
					break;
				default:
					SysBeep(5);
					goto GET_B5RESPONSE2;
				}
			printf("\n\nPRINT PATHS CONNECTING FACES OF EACH DIAGRAM ? HIT 'y' OR 'n'.    ");
			GET_B5RESPONSE3:
			switch(WaitkbHit())
				{
				case 'y':
					B5PrintPaths = TRUE;
					break;
				case 'n':
					B5PrintPaths = FALSE;
					break;
				default:
					SysBeep(5);
					goto GET_B5RESPONSE3;
				}
			if(B5PrintPaths)
				{	
				printf("\n\nCHECK SIMPLE CIRCUITS FOR PRIMITIVITY ETC ? HIT 'y' OR 'n'.    ");
				GET_B5RESPONSE4:
				switch(WaitkbHit())
					{
					case 'y':
						B5TestSimpleCircuits = TRUE;
						break;
					case 'n':
						B5TestSimpleCircuits = FALSE;
						break;
					default:
						SysBeep(5);
						goto GET_B5RESPONSE4;
					}
				}						
			break;
			
		case 'D':
			Batch = 51;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				printf("\n\nRewrite Dual Relators in Canonical Form ? HIT 'y' OR 'n'.    ");
				GET_B51RESPONSE1:
				switch(WaitkbHit())
					{
					case 'y':
						B51RewriteDualRelators = TRUE;
						fprintf(H_Results,"\nBatch option 'D', Rewrite_Dual_Relators = TRUE ");
						break;
					case 'n':
						B51RewriteDualRelators = FALSE;
						fprintf(H_Results,"\nBatch option 'D', Rewrite_Dual_Relators = FALSE ");
						break;
					default:
						SysBeep(5);
						goto GET_B51RESPONSE1;
					} 					
				fprintf(H_Results,"\n\nThe relators dual to each realizable initial presentation should appear below.");
				}
			break;
					
		case 'E':
			Batch = 57;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) fprintf(H_Results,"\nBatch option 'E' ");
			break;
								
		case 'f':
			Batch = 55;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'f'. ");
				fprintf(H_Results,"Checked whether groups of the form G = < A,B | R > have f.g commutator subgroups. ");
				fprintf(H_Results,"F indicates a f.g. commutator subgroup, NF indicates not f.g., ? indicates indeterminate ");
				fprintf(H_Results,"e.g. G has more than 2-generators, or R abelianizes to (0,0) etc.");
				}
			break;

		case 'g':
			Batch = 3;
			BNumIndeterminate = BNumNotRealizable = BNumNotConnected = BNumEmpty = BNumTooLong = NumRealizable = 0;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) fprintf(H_Results,"\nBatch option 'g' ");
			break;
														
		case 'h':
			Batch = 6;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{ 
				fprintf(H_Results,"\nBatch option 'h' ");
				fprintf(H_Results,"\n\nThe Z-homology of each initial presentation should appear below.");
				}			
			break;
			
		case 'l':
			Batch = 7;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'l' ");
				fprintf(H_Results,"\n\nInfo about the orbits under level-transformations of each initial presentation should appear below.");
				}	
			break;

		case 'L':
			Batch = 58;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'L' ");
				fprintf(H_Results,"\n\nInfo about existence of non-minimal, unstabilized splittings should appear below.");
				}
			SetLimits();
			MyMaxSavedPres3 = MyMaxSavedPres;
			MyMaxNumDiagrams3 = MyMaxNumDiagrams;
			TargetNumGenerators = NumGenerators;	
			break;
						
		case 'm':
			Batch = 8;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'm' ");
				fprintf(H_Results,"\n\nInfo about pseudo-minimality of each initial presentation should appear below.");
				}
			break;
			
		case 'p':
			Batch = 54;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'p' ");
				fprintf(H_Results,"\n\nInfo about positivity of each 1-relator, 2-generator presentation should appear below.");
				fprintf(H_Results,"P indicates there is a basis for H in which R is positive. NP indicates there is no such basis.");
				fprintf(H_Results,"? indicates more than two generators exist, or some problem occurred.");
				}
			break;
																			
		case 'q':
			fseek(input_relators,0L,0);
			if(NumFilled) Delete_Old_Presentations();
    		Init_G_Variables();
    		NumFilled = 0;
			return(0);
				
		case 'r':
			Batch = 10;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL)
				{
				fprintf(H_Results,"\nBatch option 'r', ");		
				Set_Up_Simplification_Parameters(&SFormBandsums,&SOnlyReducingBandsums,
					&SDelete_Only_Short_Primitives, &SDo_Not_Reduce_Genus);
				Set_Up_Simplification_Parameters_S1();
				}										               
			break;
					
		 case 'R':
		 	Batch = 11;	
		 	H_Results = fopen("Heegaard_Results","a+");
		 	if(H_Results != NULL)
		 		{
		 		fprintf(H_Results,"\nBatch option 'R', ");
				Set_Up_Simplification_Parameters(&SFormBandsums,&SOnlyReducingBandsums,
					&SDelete_Only_Short_Primitives, &SDo_Not_Reduce_Genus);					
				Set_Up_Simplification_Parameters_S1();
				}								 		 	
			break;
						
		case 's':
			Batch = 12;
			break;
			
		case 'S':
			SnapPy2Heegaard();
			goto END;
			
		case 'T':
			ReRun_Batches_Of_Bunches();
			goto END;
							
		case 'u':
			Batch = 13;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'u', ");
				fprintf(H_Results,"\n\nA stabilized version of each initial presentation should appear below.");
				}			
			break;
				
		case 'U':
			Batch = 53;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) fprintf(H_Results,"\nBatch option 'U' ");
			SetLimits();
			break;
					
		case 'W':
			ReRun_Batches_Of_Bunches2();
			goto END;
				
		case 'x':
			Batch = 14;
			printf("\n\n'x' PRINTS A MIN GEN, MIN REL, MIN LENGTH REP FOUND BY DELETING PRIMITIVES FROM THE IP TO THE TERMINAL.");
			printf("\nALSO SAVE THIS MIN REP TO 'Heegaard_Results' ? HIT 'y' OR 'n'.    ");
			GET_B14RESPONSE1:
			switch(WaitkbHit())
				{
				case 'y':
					B14B15PrintPres = TRUE;
					H_Results = fopen("Heegaard_Results","a+");
					if(H_Results != NULL) fprintf(H_Results,"\nBatch option 'x', PrintPres = TRUE ");
					break;
				case 'n':
					B14B15PrintPres = FALSE;
					break;
				default:
					SysBeep(5);
					goto GET_B14RESPONSE1;
				}
			break;
					
		case 'X':
			Batch = 15;
			printf("\n\n'X' PRINTS THE NUMBER OF PRIMITIVE RELATORS IN THE IP TO THE TERMINAL.");
			printf("\nALSO SAVE THIS INFO TO 'Heegaard_Results' ? HIT 'y' OR 'n'.    ");
			GET_B15RESPONSE1:
			switch(WaitkbHit())
				{
				case 'y':
					B14B15PrintPres = TRUE;
					H_Results = fopen("Heegaard_Results","a+");
					if(H_Results != NULL) fprintf(H_Results,"\nBatch option 'X', PrintPres = TRUE ");
					break;
				case 'n':
					B14B15PrintPres = FALSE;
					break;
				default:
					SysBeep(5);
					goto GET_B15RESPONSE1;
				}			
			break;
									   
		case 'z':
			Batch = 16;
			Min_Length_Parameter = Get_Min_Length_Parameter();			
			H_Results = fopen("Heegaard_Results","a+");			
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'z'");
				if(Min_Length_Parameter) fprintf(H_Results,". Minimized lengths of relators 1 -> %d of each presentation.",Min_Length_Parameter);
				fprintf(H_Results,"\n\nA minimal length version of each initial presentation should appear below.");
				}	
			Turn_Micro_Print_On();
			SMicro_Print = Micro_Print;
			SMicro_Print_F = Micro_Print_F;	
			break;
			
		case 'Z':
			Batch = 17;
			H_Results = fopen("Heegaard_Results","a+");
			if(H_Results != NULL) 
				{
				fprintf(H_Results,"\nBatch option 'Z' ");
				fprintf(H_Results,"\n\nNote DSC < FR! indicates there are simple circuits of less than full rank disjoint from the relators.");
				}
			break;
								
		default:
			SysBeep(5);
			goto GET_RESPONSE3;
		}
 
    fseek(input_relators,0L,0);
    Delete_Old_Presentations();
    NumPresExamined = 0;
    Stop = FALSE;        
	while(1)
		{
		if('s' == mykbhit()) 
			{
			printf("\n	Status: Processed %u presentations. Hit 'c' to continue. Hit 'q' to abort.    ",NumPresExamined);
			GET_RESPONSE2:			
			switch(WaitkbHit())
				{
				case 'c':
					break;
				case 'q':
					{
					fseek(input_relators,0L,0);
    				Delete_Old_Presentations();
    				Init_G_Variables();
    				NumFilled = 0;
					goto OPTIONS;		
					}
				default: goto GET_RESPONSE2;
				}	
			}
		
		if(Get_Next_Presentation_From_File(TRUE)) break;
		
		/**************************************************************************************
            Echo the initial relators to the output so we will have a copy of them. Then call
            Freely_Reduce(), Rewrite_Input(), and Canonical_Rewrite() to get a presentation
            which serves as the initial presentation for Heegaard. 
        **************************************************************************************/    
        
        NumPresExamined ++;
        
        Micro_Print 	= FALSE;
       	Micro_Print_F 	= FALSE;
        for(i = 1,Scratch = 0L; i <= NumRelators; i++)
            Scratch += GetHandleSize((char **) Relators[i]);
        Scratch -= NumRelators;
        if(Batch != 3) printf("\n\nHas L %ld, ",Scratch);        									
        if(Freely_Reduce() == TOO_LONG)
            {
            printf(" <-- TOO LONG!");
        	if(H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- TOO LONG!",PresName);
        	if(Batch == 3) BNumTooLong ++;
			continue;
            }
        if(Scratch > OrigLength)
            {
            printf("and freely reduces to the following presentation of length %lu.\n",
                OrigLength);
            Print_Relators(Relators,NumRelators);
            printf("\n\n");
            Scratch = OrigLength;
            if(Batch == 4 || Batch == 53)
            	{
            	printf("\nSince the original presentation is not freely reduced, it is not a Heegaard Splitting Rep!");
				if(H_Results != NULL) fprintf(H_Results,"\n\n%s <-- Not a HS Rep! (IP not freely reduced.)",PresName);	            	
            	continue;
            	}
            }   
        if(Rewrite_Input())
            {
            printf("\n\n------------------------------------");        	
        	printf("\n\n%s <-- Empty!",PresName);
        	if(H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- Empty!",PresName);
        	if(Batch == 3) BNumEmpty ++;
			continue;
            }   

        /**************************************************************************************
            Save a copy of the initial set of relators in case we want to refer to them later.
        **************************************************************************************/
        
        CopyNumRelators     = NumRelators;
        CopyNumGenerators   = NumGenerators;
        HS_Rep_Length 		= OrigLength;
        HS_Rep_NumGens		= NumGenerators;
        for(i = 1; i <= NumRelators; i++)
            {
            if(Copy_Of_Input[i] != NULL) DisposeHandle((char **) Copy_Of_Input[i]);
            Copy_Of_Input[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
            if(Copy_Of_Input[i] == NULL) Mem_Error();
            p = *Copy_Of_Input[i];
            q = *Relators[i];
            while( (*p++ = *q++) ) ;
            }
                                        
        /**************************************************************************************
                Call Init_G_Variables() to initialize some global variables. Then call
                Canonical_Rewrite() to rewrite the presentation in canonical form.
        **************************************************************************************/
        
        Init_G_Variables();
        Length = Scratch;
        if(Batch != 3) printf("Gen %d, Rel %d.\n\n",NumGenerators,NumRelators);
        
        Micro_Print = TRUE;					
        if(Canonical_Rewrite(Relators,FALSE,FALSE) == TOO_LONG) printf("\n\nThis presentation has too many symmetries!!"); 
        Micro_Print = FALSE;					                         
        if(Compare_Input_Pres() == FALSE)
            {
            printf("\n\n The rewritten presentation is:");
            Print_Relators(Relators,NumRelators);
            printf("\n");
            if(Batch == 4 || Batch == 53)
            	{
           		printf("\nThe IP is not written in Canonical Form. Hence it is not a Heegaard Splitting Rep!");
				if(H_Results != NULL) fprintf(H_Results,"\n\n%s <-- Not a HS Rep! (IP not in Canonical Form.)",PresName);	            	
            	continue;            	
            	}
            }
        					
        /**************************************************************************************
                        Update the copy of the initial set of relators.
        **************************************************************************************/
        
        CopyNumRelators       = NumRelators;
        CopyNumGenerators     = NumGenerators;
        for(i = 1; i <= NumRelators; i++)
            {
            if(Copy_Of_Input[i] != NULL) DisposeHandle((char **) Copy_Of_Input[i]);
            Copy_Of_Input[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Relators[i]));
	        if(Copy_Of_Input[i] == NULL) Mem_Error();    
            p = *Copy_Of_Input[i];
            q = *Relators[i];
            while( (*p++ = *q++) ) ;
            }    
		
		switch(Batch)
			{
			case 1:
				if(NumGenerators != 2 || NumRelators != 1) continue;
				AlexanderPolynomial(*Relators[1]); 
				break;
				
			case 2:
				if(Genus_Two_Meridian_Reps(0,0) && H_Results != NULL) fprintf(H_Results,"\n\n%s ?",PresName);
				break;
				
			case 3:
				Sum = BNumNotRealizable + BNumNotConnected + BNumEmpty + BNumTooLong + NumRealizable;
				Check_Realizability_Of_The_Initial_Presentation();
				if(Sum == (BNumNotRealizable + BNumNotConnected + BNumEmpty + BNumTooLong + NumRealizable))
					{
					BNumIndeterminate ++;
					if(H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- Indeterminate or Not Unique!",PresName);
					}
				break;
				
			case 4:	
				Check_If_HS_Rep 	= TRUE;
				DepthFirstSearch	= FALSE;
				BreadthFirstSearch	= TRUE;
				Find_All_Min_Pres 	= FALSE;
				CheckHSReps 		= TRUE;
				Delete_Only_Short_Primitives 	= FALSE;
    			Do_Not_Reduce_Genus 			= FALSE;
    			FormBandsums 					= TRUE;
    			OnlyReducingBandsums 			= FALSE;
    			BPrintAnnulusData 				= FALSE;
    			BPrintNotConnectedData 			= FALSE;
    			switch(Just_Delete_Primitives(TRUE,TRUE))
    				{
    				case 0:
    					break;
    				case 1:
    					printf(" Since this presentation contains primitives, it is not a HS Rep!");
						if(H_Results != NULL) fprintf(H_Results,"\n\n%s <-- Not a HS Rep!",PresName);    					
    					continue;
    				case 3:
    					continue;	
    				case INTERRUPT:
    					{
    					Stop = TRUE;
    					break;
    					}
    				default:
    					break;
    				}
    			NumFilled = 0;	
    			/* Reset the Relators */
                NumRelators = CopyNumRelators;
                if(NumRelators == 1) continue;
        		NumGenerators = CopyNumGenerators;
        		Vertices = 2*NumGenerators;
				for(i = 1; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Input[i]));
					if(Relators[i] == NULL) Mem_Error();    
					p = *Copy_Of_Input[i];
					q = *Relators[i];
					while( (*q++ = *p++) ) ;
					}
    			if(Get_Initial_Diagram(TRUE)) continue;
    			TestRealizability1 = FALSE;
    			TestRealizability2 = FALSE;
    			Mergers = 0;          
    			if(Get_Diagrams() == INTERRUPT) 
    				{
    				Stop = TRUE;			
    				break;
    				}
    			if(NumFilled >= MyMaxSavedPres || OnStack == 0) printf("\n%s is probably a HS Rep!",PresName);	
				if(H_Results != NULL && (NumFilled >= MyMaxSavedPres || OnStack == 0))
					fprintf(H_Results,"\n\n%s \nProbably a HS Rep!",PresName);  		
				break;
				
			case 5:
				Display_Diagram_Of_The_Initial_Presentation();
				break;
				
			case 6:
				Compute_Homology(FALSE);
				break;
				
			case 7:
				Fill_A(NumRelators);
				ComputeValences_A();
				if(Find_Level_Transformations_Of_The_Initial_Presentation() == 0)
					Test_LT_For_Pseudo_Min();
				DrawingDiagrams 		 = FALSE;
                Did_Exponent_Surgery 	 = FALSE;
                Did_Cutting_Disk_Surgery = FALSE;
				Delete_Old_Presentations();
				NumFilled = 0;
				break;
				
			case 8:
				i = PM_Check_When_Bdry_Exists(2);								
				switch(i)
					{
					case 1: /* Bdry !PM */
						printf("%s <-- Bdry & !PM",PresName);
						fprintf(H_Results,"\n\n%-19s <-- Bdry & !PM",PresName);
						break;        	
					case 2: /* Bdry & PM */
						printf("%s <-- Bdry & PM",PresName);
						fprintf(H_Results,"\n\n%-19s <-- Bdry & PM",PresName);
						break;        	
					case 3: /* Bdry & QPM */ 
						printf("%s <-- Bdry & QPM",PresName);
						fprintf(H_Results,"\n\n%-19s <-- Bdry & QPM",PresName);
						break;
					case 4:	/* Closed */
						SLength = Length;
						for(i = 1; i <= NumRelators; i++)
							{ 
							Temp                = Relators[i];
							Relators[i]         = DualRelators[i];
							DualRelators[i]     = Temp;    
							}
						if(Freely_Reduce() == TOO_LONG)
							{
							printf("%s <-- ?",PresName);
							fprintf(H_Results,"\n\n%-19s <-- ?",PresName);
							break;
							}
						Length = OrigLength;
						Find_Flow_A(NORMAL,FALSE);
						if(Length == SLength) 
							{
							printf("%s <-- Closed & PM",PresName);
							fprintf(H_Results,"\n\n%-19s <-- Closed & PM",PresName);
							}
						else 
							{
							printf("%s <-- Closed & !PM",PresName);
							fprintf(H_Results,"\n\n%-19s <-- Closed & !PM",PresName);
							}  
						break;
					case 5: /* Closed & Redundant Relators */ 
						printf("%s <-- Closed with Redundant Relators!",PresName);
						fprintf(H_Results,"\n\n%-19s <-- Closed with Redundant Relators!",PresName);      	
						break;
					case 6: /* Length-Reducing Bandsum. */
						printf("%s <-- Bdry & !QPM",PresName); 
						fprintf(H_Results,"\n\n%-19s <-- Bdry & !QPM",PresName);       	
						break;
					case SEP_PAIRS:
						printf("%s <-- ? Sep Pairs",PresName); 
						fprintf(H_Results,"\n\n%-19s <-- ? Sep Pairs",PresName);       	
						break;							
					case TOO_LONG:
						printf("%s <-- ?",PresName);
						fprintf(H_Results,"\n\n%-19s <-- ?",PresName);
						break;	
					default:
						break;	
					}				
				break;
									
			case 10:
				DepthFirstSearch	= TRUE;
				BreadthFirstSearch	= FALSE;
				Find_All_Min_Pres 	= FALSE;
				Delete_Only_Short_Primitives 	= SDelete_Only_Short_Primitives;
    			Do_Not_Reduce_Genus 			= SDo_Not_Reduce_Genus;  			
    			FormBandsums 					= SFormBandsums;
    			OnlyReducingBandsums 			= SOnlyReducingBandsums;
    			if(Get_Initial_Diagram(TRUE)) 
    				{
    				if(H_Results) fprintf(H_Results,"\n------------------------------------\n%-19s",PresName);
					if(NumRelators == 1 && NumGenerators == 2)
						{
						i = Genus_Two_One_Relator_Annuli_And_Tori(TRUE,TRUE,FALSE);
						if(i == 0) 
							{
							printf("\nH[R] is anannular and atoroidal.");
							if(H_Results != NULL) fprintf(H_Results,"<-- H[R] is anannular and atoroidal."); 
							}
						}
					if((NumRelators != 1 || NumGenerators != 2) && H_Results) 
						fprintf(H_Results,"<-- No HS Reps!");
					continue;
					}					
    			TestRealizability1 = FALSE;
    			TestRealizability2 = FALSE;           
	   			if(Get_Diagrams() == INTERRUPT) 
	   				{
	   				Stop = TRUE;
	   				break;
	   				}							
    			Sort_Presentations_In_Memory(1); 			
    			Delete_Old_Presentations();
    			break; 
    			   			
			case 11:
				DepthFirstSearch	= FALSE;
				BreadthFirstSearch	= TRUE;
				Find_All_Min_Pres 	= FALSE;
				Delete_Only_Short_Primitives 	= SDelete_Only_Short_Primitives;
    			Do_Not_Reduce_Genus 			= SDo_Not_Reduce_Genus;
    			FormBandsums 					= SFormBandsums;
    			OnlyReducingBandsums 			= SOnlyReducingBandsums;
    			if(Get_Initial_Diagram(TRUE)) 
					{
    				if(H_Results) fprintf(H_Results,"\n------------------------------------\n%-19s",PresName);
					if(NumRelators == 1 && NumGenerators == 2)
						{
						i = Genus_Two_One_Relator_Annuli_And_Tori(TRUE,TRUE,FALSE);
						if(i == 0) 
							{
							printf("\nH[R] is anannular and atoroidal.");
							if(H_Results != NULL) fprintf(H_Results,"<-- H[R] is anannular and atoroidal."); 
							}
						}
					if((NumRelators != 1 || NumGenerators != 2) && H_Results) 
						fprintf(H_Results,"<-- No HS Reps!");
					continue;
					}
    			TestRealizability1 = FALSE;
    			TestRealizability2 = FALSE;           
    			if(Get_Diagrams() == INTERRUPT) 
    				{
    				Stop = TRUE;
    				break;
    				}
    			Sort_Presentations_In_Memory(1); 
    			Delete_Old_Presentations(); 					
				break;
				
			case 12:
				Find_Symmetries(FALSE);
				break;
				
			case 13:
				Stabilize(TRUE);
				break;
				
			case 14:
    			if(Just_Delete_Primitives(FALSE,TRUE) == INTERRUPT) 
    				{
    				Stop = TRUE;
    				break;
    				}
				break;
				
			case 15:
    			if(Just_Delete_Primitives(TRUE,TRUE) == INTERRUPT) 
    				{
    				Stop = TRUE;
    				break;
    				}
				break;
				
			case 16:				
        		Micro_Print = SMicro_Print;
        		Micro_Print_F = SMicro_Print_F;	
				Reduce_The_Initial_Presentation_To_Minimal_Length(Min_Length_Parameter);
				break;
				
			case 17:
				if(Find_Simple_Circuits()) 
					{
					printf("Has DSC < FR!");
					fprintf(H_Results,"\n\n%-19s <-- Has DSC < FR!",PresName);
					}
				else 
					{
					printf("No DSC < FR!");
					fprintf(H_Results,"\n\n%-19s <-- No DSC < FR!",PresName);
					}
				break;
					
			case 51:
				Fill_A(NumRelators);				
				if(ComputeValences_A()) break;
				Get_Matrix();
				for(i = 0; i < Vertices; i++) ZZ[i] = 0;
				if(Connected_(0,0) == FALSE) break;
				if(Sep_Pairs(0,0,1)) break;
				if(Planar(FALSE,TRUE) == TRUE) break;
				Diagram_Main();
				break;
				
			case 53:
				DepthFirstSearch	= FALSE;
				BreadthFirstSearch	= TRUE;
				Find_All_Min_Pres 	= FALSE;
				CheckHSReps 		= TRUE;
				Delete_Only_Short_Primitives 	= FALSE;
    			Do_Not_Reduce_Genus 			= FALSE;
    			FormBandsums 					= TRUE;
    			OnlyReducingBandsums 			= FALSE;
    			BPrintAnnulusData 				= FALSE;
    			BPrintNotConnectedData 			= FALSE;
    			switch(Just_Delete_Primitives(TRUE,TRUE))
    				{
    				case 0:
    					break;
    				case 1:
    					printf(" Since this presentation contains primitives, it is not a HS Rep!");
						if(H_Results != NULL) fprintf(H_Results,"\n\n%s <-- Not a HS Rep! (IP contains primitives.)",PresName);    					
    					continue;
    				case 3:
    					continue;	
    				case INTERRUPT:
    					{
    					Stop = TRUE;
    					break;
    					}
    				default:
    					break;
    				}
    			NumFilled = 0;	
    			/* Reset the Relators */
                NumRelators = CopyNumRelators;
        		NumGenerators = CopyNumGenerators;
        		Vertices = 2*NumGenerators;
				for(i = 1; i <= NumRelators; i++)
					{
					if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
					Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) Copy_Of_Input[i]));
					if(Relators[i] == NULL) Mem_Error();    
					p = *Copy_Of_Input[i];
					q = *Relators[i];
					while( (*q++ = *p++) ) ;
					}
				if(Reduce_The_Initial_Presentation_To_Minimal_Length(0))
					{
					printf("\n\nThe IP does not have minimal length. Hence is not a HS Rep!");
					if(H_Results != NULL)
						fprintf(H_Results,"\n\n%s  <-- Not a HS Rep! (IP does not have minimal length.)",PresName);
					continue;	
					}			
				if(Stabilize(TRUE)) continue;	
    			if(Get_Initial_Diagram(TRUE)) continue;	
    			TestRealizability1 = FALSE;
    			TestRealizability2 = FALSE;
    			printf("\n\nThe minimal length stabilized presentation is:");
    			Print_Relators(Relators,NumRelators);
	   			if(Get_Diagrams() == INTERRUPT)
    				{
    				Stop = TRUE;			
    				break;
    				} 
    			if(Sort_Presentations_In_Memory(FALSE) == INTERRUPT) Stop = TRUE;	 		
				break;
				
			case 54:
				if(NumRelators != 1 || NumGenerators != 2) continue;			
				i = Check_R1_Positivity();
				if(i == 0) printf("  NP");
				if(i == 1) printf("  P");
				if(i == 2) printf("  ?");				
				if(H_Results != NULL)
					{
					if(i == 0) fprintf(H_Results, "\n\n%s  <-- NP",PresName);
					if(i == 1) fprintf(H_Results, "\n\n%s  <-- P",PresName);
					if(i == 2) fprintf(H_Results, "\n\n%s  <-- ?",PresName);
					}
				break;
				
			case 55:
				if(NumRelators != 1 || NumGenerators != 2) continue;
				i = Check_If_Fibered(*Relators[1]);
				if(H_Results != NULL)
					{
					if(i == 0) fprintf(H_Results, "\n\n%s  <-- NF",PresName);
					if(i == 1) fprintf(H_Results, "\n\n%s  <-- F",PresName);
					if(i == 2) fprintf(H_Results, "\n\n%s  <-- ?",PresName);
					}							
				break;
				
			case 56:
				if(NumRelators != 1 || NumGenerators != 2) continue;
				i = Genus_Two_One_Relator_Annuli_And_Tori(TRUE,TRUE,FALSE);
            	if(i == 0) 
            		{
            		printf("\nH[R] is anannular and atoroidal.");
            		if(H_Results != NULL) fprintf(H_Results,"%-19s <-- H[R] is anannular and atoroidal.",PresName); 
            		}
            	break;
            	
            case 57:
            	if(NumRelators != 2 || NumGenerators != 2) continue;
				i = Get_Universal_Minimizer_Waves(TRUE);
				if(i < 5) printf("\n?");
				if(i == 5) printf("\nUniversal Minimizers.");
				if(i == 6) printf("\nUniversal Minimizers, Distance >= 3, Hyperbolic.");
				if(i == 7) printf("\nUniversal Minimizers, Distance >= 3, Hyperbolic, and, since no (PP,SF) curves, a Unique splitting.");
				if(i == 8) printf("\nUniversal Minimizers, Distance 2.");				
				if(H_Results != NULL)
					{
					if(i < 5) fprintf(H_Results,"\n\n%-19s <-- ?",PresName);
					if(i == 5) fprintf(H_Results,"\n\n%-19s <-- Universal Minimizers",PresName);
					if(i == 6) fprintf(H_Results,"\n\n%-19s <-- Universal Minimizers, Hyperbolic, Distance >= 3",PresName);
					if(i == 7) fprintf(H_Results,"\n\n%-19s <-- Universal Minimizers, Hyperbolic, Distance >= 3, Unique splitting",PresName);	
					if(i == 8) fprintf(H_Results,"\n\n%-19s <-- Universal Minimizers, Distance 2.",PresName);					
					}
				break;
			
			case 58:
				if(H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- ",PresName);
				Batch = FALSE;
				I =	Search_For_Non_Minimal_UnStabilized_Splittings(TRUE,TargetNumGenerators);
				if(I == QUIT_FLAG) 
					{
					if(H_Results != NULL) fprintf(H_Results,"?");
					Check_for_1_HS = FALSE;
					Stop = TRUE;
					Batch = 58;
					break;
					}
				if(I <= 0 && H_Results != NULL) fprintf(H_Results,"?");
				if(I == 1 && H_Results != NULL) fprintf(H_Results,"1 HS");
				if(I > 1 && H_Results != NULL)  fprintf(H_Results,"%d HS",I);
				Batch = 58;
				break;										
			}
		if(Stop) break;	
		}
		
	printf("\n\n Totals: PresExamined %u",NumPresExamined);
	if(H_Results != NULL) fprintf(H_Results,"\n\n Totals: PresExamined %u",NumPresExamined);
	switch(Batch)
		{
		case 3: printf(", Realizable %u",NumRealizable);
				if(BNumNotRealizable) printf(", NotRealizable %u",BNumNotRealizable);
				if(BNumEmpty) printf(", Empty %u",BNumEmpty);
				if(BNumTooLong) printf(", TooLong %u",BNumTooLong);
				if(BNumNotConnected) printf(", Not Connected %u",BNumNotConnected);
				if(BNumIndeterminate) printf(", Indeterminate or Not Unique %u",BNumIndeterminate);
				if(H_Results != NULL)
					{
					fprintf(H_Results,", Realizable %u",NumRealizable);
					if(BNumNotRealizable) fprintf(H_Results,", NotRealizable %u",BNumNotRealizable);
					if(BNumEmpty) fprintf(H_Results,", Empty %u",BNumEmpty);
					if(BNumTooLong) fprintf(H_Results,", TooLong %u",BNumTooLong);
					if(BNumNotConnected) fprintf(H_Results,", Not Connected %u",BNumNotConnected);
					if(BNumIndeterminate) fprintf(H_Results,", Indeterminate or Not Unique %u",BNumIndeterminate);
					}
				break;	
		}
	fclose(input_relators);
	if(H_Results != NULL) switch(Batch)
		{
		case 1:
			printf("\n\nAlexander polynomials of each 1-relator, 2-generator IP should appear in 'Heegaard_Results'.");
			break;
		case 2:			
			printf("\n\n'Meridian reps of each realizable 1-relator, 2-generator IP should appear in 'Heegaard_Results'.");
			break;		
		case 3:
			printf("\n\nEach IP's realizability should appear in 'Heegaard_Results'.");
			break;	
		case 4:
			printf("\n\nIndication that the IP is a Heegaard Splitting Rep should appear in 'Heegaard_Results'.");
			break;
		case 6:
			printf("\n\nEach IP's Z-homology should appear in 'Heegaard_Results'.");
			break;
		case 7:
			printf("\n\nOrbit under level-transformations info for each IP should appear in 'Heegaard_Results'.");
			break;
		case 10:
			printf("\n\nResults should appear in 'Heegaard_Results'.");
			break;
		case 11:
			printf("\n\nResults should appear in 'Heegaard_Results'.");
			break;										
		case 13:
			printf("\n\nStabilized IP's should appear in 'Heegaard_Results'.");
			break;
		case 14:
			printf("\n\nA Min Gen, Min Length Rep found of each IP should appear in 'Heegaard_Results'.");
			break;
		case 15:
			printf("\n\nThe number of primitives in each IP should appear in 'Heegaard_Results'.");
			break;
		case 16:
			printf("\n\nMinimal length versions of each IP should appear in 'Heegaard_Results'.");
			break;
		case 17:
			break;	
		case 51:
			printf("\n\nThe dual relators of each presentation should appear in 'Heegaard_Results'.");
			break;
		case 53:
			printf("\n\nHS Rep data for each IP should appear in 'Heegaard_Results'.");
			break;
		case 54:
			printf("\n\nPositivity, Non-positivity results for 1-relator, 2-generator presentations should appear in 'Heegaard_Results'.");
			break;
		case 55:
			printf("\n\nWhether groups of the form G = < A,B | R > have f.g. commutator subgroups should appear in 'Heegaard_Results'.");
			break;
		case 56:
			printf("\n\nWhether 1-relator, 2-generator manifolds H[R] are annular or toroidal should appear in 'Heegaard_Results'.");
			break;
		case 57:
			printf("\n\nWhether 2-relator, 2-generator manifolds H[R] have Universal Minimizers should appear in 'Heegaard_Results'.");
			break;
		case 58:
			printf("\n\nInfo about the existence of non-minimal, unstabilized splittings should appear in 'Heegaard_Results'.");												
		default:
			break;	
		}
		
END:	
	if(H_Results != NULL) 
		{
		fclose(H_Results);
		H_Results = NULL;
		}
	if(H_Results_2 != NULL) 
		{
		fclose(H_Results_2);
		H_Results_2 = NULL;
		}	
	SysBeep(5);	
	printf("\n\nHIT 'B' TO CONTINUE IN 'BATCH' MODE. HIT 'q' TO QUIT RUNNING IN BATCH MODE.    ");
	GET_RESPONSE4:
	switch(WaitkbHit())
		{
		case 'B': 
			goto OPTIONS;
		case 'q':
			fseek(input_relators,0L,0);
			if(NumFilled) Delete_Old_Presentations();
			Init_G_Variables();
			NumFilled = 0;
			return(0);
		default:
			SysBeep(5);
			goto GET_RESPONSE4;
		}
}

int Set_Up_Simplification_Parameters(int* SFormBandsums, int* SOnlyReducingBandsums,
	int* SDelete_Only_Short_Primitives, int* SDo_Not_Reduce_Genus)
{

	printf("\n\nCREATE NEW DIAGRAMS BY FORMING BANDSUMS ? HIT 'y' OR 'n'.    ");
	GET_RESPONSE1:       
	switch(WaitkbHit())
		{
		case 'y':
			printf("\n    HIT 'a' TO FORM ALL POSSIBLE BANDSUMS.");
			printf("\n    HIT 'r' TO FORM ONLY LENGTH REDUCING BANDSUMS.");
			printf("\n    HIT 'n' TO FORM NO BANDSUMS.    ");
			fprintf(H_Results,"BandSums 'y', ");
			GET_RESPONSE2:               
			switch(WaitkbHit())
				{
				case 'a':
					*SFormBandsums 			= TRUE;
					*SOnlyReducingBandsums 	= FALSE;
					fprintf(H_Results,"BandSums Option 'a', ");
					break;
				case 'r':
					*SFormBandsums 			= TRUE;
					*SOnlyReducingBandsums 	= TRUE;
					fprintf(H_Results,"BandSums Option 'r', ");
					break;
				case 'n':
					*SOnlyReducingBandsums = *SFormBandsums = FALSE;
					fprintf(H_Results,"BandSums Option 'n', ");
					break;    
				default:
					SysBeep(5);
					goto GET_RESPONSE2;
				}
			printf("\n");    
			break;        
		case 'n':
			*SOnlyReducingBandsums = *SFormBandsums = FALSE;
			fprintf(H_Results,"BandSums 'n', ");               
			break;
		default:
			SysBeep(5);
			goto GET_RESPONSE1;    
		} 
		
	printf("\n\nDELETE ALL PRIMITIVE RELATORS AFTER CHECKING REALIZABILITY ? HIT 'y' OR 'n'.");
	printf("\nNote choosing 'n' turns off lens space and genus two essential torus recognition.    ");
    
    GET_RESPONSE3:   
    switch(WaitkbHit())
        {
        case 'y':
            *SDo_Not_Reduce_Genus 			= FALSE;
            *SDelete_Only_Short_Primitives 	= FALSE;
            fprintf(H_Results,"Delete Primitives 'y', ");
            break;
        case 'n':    
            printf("\n\nDELETE PRIMITIVE RELATORS OF LENGTH 1 AND LENGTH 2 ? HIT 'y' OR 'n'.    ");
            fprintf(H_Results,"Delete Primitives 'n', ");
            GET_RESPONSE4:            
            switch(WaitkbHit())
                {
                case 'y':
                    *SDelete_Only_Short_Primitives 	= TRUE;
                    fprintf(H_Results,"Delete Primitives Option 'y', ");
                    *SDo_Not_Reduce_Genus 			= FALSE;
                    break;
                case 'n':
                    *SDelete_Only_Short_Primitives 	= FALSE;
                    fprintf(H_Results,"Delete Primitives Option 'n', ");
                    *SDo_Not_Reduce_Genus 			= TRUE;
                    break;
                default:
                    SysBeep(5);
                    goto GET_RESPONSE4;
                }
            break;
        default:
            SysBeep(5);
            goto GET_RESPONSE3;
        }
     
    printf("\n\n	SOME TERMINAL PRINTING OPTIONS:");    
    printf("\n1) PRINT INFO ABOUT ANNULI HEEGAARD FINDS ?");
    printf("\n2) PRINT INFO ABOUT DISCONNECTED DIAGRAMS HEEGAARD FINDS ?");
    
	printf("\n\n1) HIT 'y' OR 'n'.    ");    
    GET_RESPONSE5:
    switch(WaitkbHit())
    	{   	
		case 'y':
			BPrintAnnulusData = TRUE;
			break;
		case 'n':
			BPrintAnnulusData = FALSE;
			break;
		default:
			SysBeep(5);
			goto GET_RESPONSE5;
		} 
		
	printf("\n2) HIT 'y' OR 'n'.    ");    
	GET_RESPONSE6:
    switch(WaitkbHit())
    	{   	
		case 'y':
			BPrintNotConnectedData = TRUE;
			break;
		case 'n':
			BPrintNotConnectedData = FALSE;
			break;
		default:
			SysBeep(5);
			goto GET_RESPONSE6;
		}
		
	return(0);	   
}

int Set_Up_Simplification_Parameters_S1(void)
{
	printf("\n\n	SOME DATA SAVING OPTIONS:");
	printf("\n3) SAVE INFO ABOUT EACH RECOGNIZED MANIFOLD TO 'Heegaard_Results' ?");
	printf("\n4) SAVE INFO ABOUT EACH FINITE MANIFOLD TO 'Heegaard_Results' ?");
	printf("\n5) SAVE 'Heegaard Splitting Reps' FOUND TO 'Heegaard_Results ?");
	
	printf("\n\n3) HIT 'y' OR 'n'.    ");
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
		printf("\n4) HIT 'y' OR 'n'.    ");		
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
	else
		printf("\n	4) UNAVAILABLE WHEN REPLY TO 3) is 'y'.");	
	
	if(!B10B11Finite && !B10B11Recognized)
		{ 
		printf("\n5) HIT 'y' OR 'n'.    ");   
		GET_RESPONSE3:   
		switch(WaitkbHit())
			{
			case 'y':
				B10B11HSReps = TRUE;
				printf("\n    HIT 1 TO SAVE ALL HS REPS FOUND TO 'Heegaard_Results'.  ");
				printf("\n    HIT 2 TO SAVE ONLY HS 1, P 1 TO 'Heegaard_Results'.  ");
				printf("\n    HIT 3 TO SAVE ALL TUNNELS OF JUST TUNNEL-NUMBER-ONE MANIFOLDS TO 'Heegaard_Results'.  ");
				printf("\n    HIT 4 TO SAVE ONLY TUNNELS OF TUNNEL-NUMBER-ONE MANIFOLDS WITH ONE TUNNEL TO 'Heegaard_Results'.    ");
				GET_RESPONSE3a:
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
						goto GET_RESPONSE3a;    
					}
				break;
			case 'n':    
				B10B11HSReps = FALSE;
				fprintf(H_Results,"Saving HS Reps = FALSE, ");
				break;
			default:
				SysBeep(5);
				goto GET_RESPONSE3;
			}
        }
    else
		printf("\n	5) UNAVAILABLE WHEN REPLY TO 2) or 3) is 'y'.");   
		
	if(B10B11Recognized)
		{
		printf("\n\nSAVE COPIES OF UNRECOGNIZED PRESENTATIONS TO 'Heegaard_Results_2' FOR FURTHER CHECKING?\n");
		printf("HIT 'y' OR 'n'.    ");
		GET_RESPONSE4:
		switch(WaitkbHit())
			{
			case 'y':
				if(H_Results_2 != NULL) fclose(H_Results_2);
				H_Results_2 = fopen("Heegaard_Results_2","a+");
				if(H_Results_2 == NULL)
				    {
					SysBeep(5);
					printf("\nUnable to open the file 'Heegaard_Results_2'.");
					}
				break;
			case 'n':
				break;
			default:
				SysBeep(5);
				goto GET_RESPONSE4;
			}
		}	 
                          		   	  
	SetLimits();
		
	return(0);	   
}

void SetLimits(void)
{
	if(Batch == 58)
		{
		printf("\n\nENTER n, 0 <= n <= 26. HEEGAARD WILL TRY TO STABILIZE UNTIL EACH PRESENTATION HAS AT LEAST n GENERATORS.    ");
		GET_RESPONSE3:
		ReadString((char *)Inst, 200);
		sscanf((char *) Inst,"%d",&NumGenerators); 
		if(NumGenerators < 0 || NumGenerators > 26)
			{   	
			SysBeep(5);
			printf("\nTarget stabilized number of generators is out of range. Please reenter it!    ");
			goto GET_RESPONSE3;
			}
		}

	printf("\n\nENTER A LIMIT <= %u FOR THE NUMBER OF PRESENTATIONS HEEGAARD SHOULD SAVE BEFORE MOVING ON.",
		MAX_SAVED_PRES - 3);   
		if(Batch == 53) 	
			printf("\n (Limits >= 10,000 may be required.)\n");
		else
			printf("\n (Smaller limits are faster.)\n"); 
	GET_RESPONSE1:	  
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%u",&MyMaxSavedPres); 
	if(MyMaxSavedPres < 1 || MyMaxSavedPres > (MAX_SAVED_PRES - 3))
		{   	
		SysBeep(5);
		printf("\nMyMaxSavedPres is out of range. Please reenter it!    ");
		goto GET_RESPONSE1;
		}
	fprintf(H_Results," Limit %u, ",MyMaxSavedPres);
	
	printf("\nENTER A LIMIT <= 100,000,000 FOR THE NUMBER OF DIAGRAMS HEEGAARD SHOULD EXAMINE BEFORE MOVING ON.\n"); 
	GET_RESPONSE2:	  
	ReadString((char *)Inst, 200);
	sscanf((char *) Inst,"%ld",&MyMaxNumDiagrams); 
	if(MyMaxNumDiagrams < 1 || MyMaxNumDiagrams > MY_MAX_NUM_DIAGRAMS)
		{   	
		SysBeep(5);
		printf("\nMyMaxNumDiagrams is out of range. Please reenter it!    ");
		goto GET_RESPONSE2;
		}		
	fprintf(H_Results," MaxNumDiagrams %ld ",MyMaxNumDiagrams);
}

int SnapPy2Heegaard(void)
{
	/************************************************************************************************
		This routine converts SnapPy style presentations into Heegaard readable input presentations.
		
		Foe example, asking SnapPY to output 'M.fundamental_group(0,0,0)' with M = K8_293(0,0) 
		results in SnapPy output of the form:
		
		K8_293(0,0)
 		Generators:
   		   a,b,c,d,e,f,g,h
		Relators:
		   CDAD
		   BcHF
		   hAGF
		   gbe
		   eHgD
		   aEf
		   BBC
		   
		Heegaard expects the line following K8_293(0,0) to be the first relator of the presentation
		of M.fundamental_group(0,0,0). SnapPy2Heegaard() simply strips out the 3 lines of SnapPy output 
		
		'Generators:
   		    a,b,c,d,e,f,g,h
		 Relators:' 
		
		leaving:
		
		K8_293(0,0)
		   CDAD
		   BcHF
		   hAGF
		   gbe
		   eHgD
		   aEf
		   BBC
		   
		which Heegaard will accept.	   	
	************************************************************************************************/
	
    unsigned char  	*Ptr1,
    				*Ptr2,
    				*Ptr3,
    				*p,
                    *q,
                    *r, 
                    Str1[10] = "Relators:";                                     
    
    Ptr1 = (unsigned char*) NewPtr(3001);
	if(Ptr1 == NULL) Mem_Error();
	Ptr2 = (unsigned char*) NewPtr(3001);
	if(Ptr2 == NULL) Mem_Error();
	Ptr3 = (unsigned char*) NewPtr(3001);
	if(Ptr3 == NULL) Mem_Error();
	
	fseek(input_relators,0L,0);
	
	*Ptr1 = EOS;
	*Ptr2 = EOS;

GET_NEXT_PRES:	
	while(1)
		{
		if(fgets((char *) Ptr3,3000,input_relators) == NULL) return(1);
		/* Check if Ptr3 starts with the string "Relators:". */
		q = Ptr3;
		r = Str1;
		while(*r && (*q++ == *r++)) ;
		if(*r == EOS) goto FOUND_SUBSTRING_STR1; /* Ptr3 starts with the string "Relators:". */
		/* Otherwise copy Ptr2 into Ptr1, copy Ptr3 into Ptr2 and put the next line into Ptr3. */
		p = Ptr2;
		q = Ptr1;
		while( (*q++ = *p++) ) ;
		p = Ptr3;
		q = Ptr2;
		while( (*q++ = *p++) ) ;
		}
	
	FOUND_SUBSTRING_STR1:
	printf("\n%s",Ptr1);
	while(1)
		{
		if(fgets((char *) Ptr2,3000,input_relators) == NULL) return(1);
		if(*Ptr2 != ' ') goto GET_NEXT_PRES;
		if(*Ptr2 == ' ') printf("%s",Ptr2);
		}
	
	if(Ptr1) DisposePtr((char*) Ptr1);
	if(Ptr2) DisposePtr((char*) Ptr2);
	if(Ptr3) DisposePtr((char*) Ptr3);
	return(0);
}

int Get_Min_Length_Parameter(void)
{
	char	c;
	
	int		j;

	printf("\n\nHIT '0' TO MINIMIZE THE LENGTH OF ALL RELATORS, OR");
	printf("\nHIT 'n' in {1,2,3,4,5,6,7,8,9} TO MINIMIZE THE LENGTH OF THE FIRST n RELATORS.    ");
	GET_RESPONSE1:
	c = WaitkbHit();
	if(isdigit(c)) 
		j = c - 48;
	else 
		goto GET_RESPONSE1;
	if(j < 0) goto GET_RESPONSE1;
	
	return(j);
}