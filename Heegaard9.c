#include "Heegaard.h"
#include "Heegaard_Dec.h"

/****************************** Functions in Heegaard9.c ***********************************
L  376 In_File(void)
L   10 Init_Find_Level_Transformations(int Print)
L   85 Test_LT_For_Pseudo_Min(void)
********************************************************************************************/
   
int Init_Find_Level_Transformations(int Print)
{
    /******************************************************************************************
        This routine should be called before Find_Level_Transformations() is called. It
        checks whether the presentation of interest has minimal length and has a connected
        Whitehead graph.
    ******************************************************************************************/
                 
    unsigned char  	*p,
    				*q;   
    						   
    int          	i;						   
    
    /******************************************************************************************
        Copy the presentation which we want level transformations for into Relators[].
    ******************************************************************************************/
    
    Length = SURL[ReadPres];
    if(Length == 0) return(1);  
        
    for(i = 1; i <= NumRelators; i++)
        {
        if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
        Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
        if(Relators[i] == NULL) Mem_Error();
        q = *Relators[i];           
        p = *SUR[ReadPres][i];
        while( (*q++ = *p++) ) ;
        }
        
    /******************************************************************************************
                    Check whether this presentation has minimal length.
        If this presentation does not have minimal length, we could still look 
        for level transformations, but it does not seem very interesting to do so.            
    ******************************************************************************************/
    
    if(Find_Flow_A(NORMAL,FALSE) == TOO_LONG)
        {
        printf("\n\nPresentation %d is too long!",ReadPres + 1);
        return(TOO_LONG);
        }
    if(Automorphisms)
        {
        if(Print)
            {
            printf("\n\nPresentation %d does not have minimal length.",ReadPres + 1);
            printf("\n\nHeegaard will only find level transformations for presentations ");
            printf("that have minimal length.");
            }
        if(Batch == 7 && H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- Not Minimal Length!",PresName);    
        return(1);
        }
                        
    /******************************************************************************************
                    Check whether the Whitehead graph of this presentation is connected.
            It is important to do this because Find_Level_Transformations() will not work
            correctly if the Whitehead graph of the presentation is not connected!!
    ******************************************************************************************/
                                
    for(i = 0; i < Vertices; i++) ZZ[i] = 0;
    if(Connected_AJ3(0,0) == FALSE)
        {
        if(Print)
            {
            printf("\n\nPresentation %d does not have a connected Whitehead graph.",
            ReadPres + 1);
            printf("\n\nHeegaard will only find level transformations for presentations ");
            printf("with connected graphs!");
            }
        if(Batch == 7 && H_Results != NULL) fprintf(H_Results,"\n\n%-19s <-- Not Connected!",PresName);    
        return(2);
        }  
    return(0);
}        

void Test_LT_For_Pseudo_Min(void)
{
    /******************************************************************************************
        This is a rather crude routine which takes the set of presentations in the orbit of a
        presentation under level transformations, and checks them for separating pairs of
        vertices, reducibility of their dual diagrams and pseudo-minimality.
    ******************************************************************************************/
        
    unsigned char   *AA,
    		    	*p,
    		    	*q,
    		    	**Temp;
                    
    unsigned int    h,
    		    	i,
		    		k = 0,
		    		Num_Bad_Diagrams,
		    		Num_Pseudo_Min,
		    		Num_QPseudo_Min;
                    
    unsigned long   SLength;                
                    
    unsigned int 	Diagram_Main();
    
    DrawingDiagrams 	= TRUE;
    TestRealizability1 	= TRUE;
    Num_QPseudo_Min = Num_Pseudo_Min = Num_Bad_Diagrams= 0;
    if(Batch != 7) printf("\n");
    
    AA = (unsigned char*) NewPtr((sizeof(char)*(NumFilled+1)));
	if(AA == NULL) Mem_Error();

	NumGenerators 	= NG[0];
	NumRelators 	= NR[0];
	Vertices 		= 2*NumGenerators;   
    for(ReadPres = 0; ReadPres < NumFilled; ReadPres++)
        {     
        /**************************************************************************************
                    Copy the presentation that we want to test into Relators[].
        **************************************************************************************/

        for(i = 1; i <= NumRelators; i++)
            {
            if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
            Relators[i] = (unsigned char **) NewHandle(GetHandleSize((char **) SUR[ReadPres][i]));
            if(Relators[i] == NULL) Mem_Error();
            q = *Relators[i];           
            p = *SUR[ReadPres][i];
            while( (*q++ = *p++) ) ;
            }
        Length = SURL[ReadPres];    
        WhichInput = ReadPres;        
        Fill_A(NumRelators);
        Saved_Vertices = 0;
        Get_Matrix();
        ComputeValences_A();
        if(Sep_Pairs(0,0,1))
        	{       	
        	Num_Bad_Diagrams ++;
        	AA[ReadPres] = 0;
        	continue;       	
        	}
        if(Planar(FALSE,TRUE))
        	{
        	printf(" <-- Not Realizable!");
        	if(Batch == 7 && H_Results != NULL) fprintf(H_Results," <-- Not Realizable!");
        	goto END;
        	}
        switch(Diagram_Main())
        	{
        	case FATAL_ERROR:
				printf(" <-- Not Realizable!");
				if(Batch == 7 && H_Results != NULL) fprintf(H_Results," <-- Not Realizable!");
				goto END;        	
        	case NON_UNIQUE_1:
        	case NON_UNIQUE_2:
        	case NON_UNIQUE_3:
        	case NON_UNIQUE_4:
        	case TOO_LONG:
        	case V2_ANNULUS_EXISTS:
        		Num_Bad_Diagrams ++;
        		AA[ReadPres] = 0;
        		continue;
        	case NO_ERROR:
        		TestRealizability1 = FALSE;
        		AA[ReadPres] = 1;
        		break;
        	default:
        		Num_Bad_Diagrams ++;
        		AA[ReadPres] = 0;
        		continue;
        	}
        h = PM_Check_When_Bdry_Exists(FALSE);
        Vertices = 2*NumGenerators;     	
		switch(h)
        	{
        	case 1: /* Bdry !PM */
				break;        	
        	case 2: /* Bdry & PM */
                Num_Pseudo_Min ++;
                AA[ReadPres] = 2;
				break;        	
        	case 3: /* Bdry & QPM */ 
        		Num_QPseudo_Min ++;
             	AA[ReadPres] = 3;
        		break;
        	case 4:	/* Closed */
                SLength = SURL[ReadPres];
                for(i = 1; i <= NumRelators; i++)
                    { 
                    Temp                = Relators[i];
                    Relators[i]         = DualRelators[i];
                    DualRelators[i]     = Temp;    
                    }
                if(Freely_Reduce() == TOO_LONG) continue;
                Length = OrigLength;
                Find_Flow_A(NORMAL,FALSE);
                if(Length == SLength)
                    {
                    Num_Pseudo_Min ++;
                    AA[ReadPres] = 2;
                    }
                Length = SLength;    
                break;
        	case 5: /* Closed & Redundant Relators */ 
        		printf(" <-- Closed with Redundant Relators!");
        		if(Batch == 7 && H_Results != NULL) fprintf(H_Results," <-- Closed with Redundant Relators!");
        		goto END;       	
        		break;
        	case 6: /* Length-Reducing Bandsum. */        	
        		break;
        	default:
        		break;	
        	}
    	}
    DrawingDiagrams = FALSE;
    TestRealizability1 = FALSE;
     
    if(Batch == 7)
    	{
		printf("|WoSepVert| %u, |QPseudoMin| %u, |PseudoMin| %u"
			,NumFilled - Num_Bad_Diagrams,Num_QPseudo_Min,Num_Pseudo_Min);  		
		if((NumFilled - Num_Bad_Diagrams) == Num_Pseudo_Min) 
			printf(", WStable");
		else
			printf(", UnStable");  		
		if(H_Results != NULL) 
			{
			fprintf(H_Results,"|WoSepVert| %u, |QPseudoMin| %u, |PseudoMin| %u"
			,NumFilled - Num_Bad_Diagrams,Num_QPseudo_Min,Num_Pseudo_Min);
			if((NumFilled - Num_Bad_Diagrams) == Num_Pseudo_Min) fprintf(H_Results,", WStable");
			else fprintf(H_Results,", UnStable");
			}
    	DisposePtr((unsigned char*) AA);
    	return;
    	}
          
    if(Num_Bad_Diagrams < NumFilled)
        {
        printf("\n\nPresentations with no separating pairs of vertices:    ");
        for(h = 0; h < NumFilled; h++) if(AA[h])
            {
            printf("{ %u",h+1);    
            break;
            }
        for(i = h + 1; i < NumFilled; i++) if(AA[i]) printf(", %u",i+1); 
        printf(" }");                  
        }    
 
    if(NumFilled > Num_Bad_Diagrams + Num_Pseudo_Min + Num_QPseudo_Min)
    	{
		printf("\n\nPresentations not Pseudo-Minimal or QPseudo_Minimal and without separating pairs of vertices:    ");
		for(h = 0; h < NumFilled; h++) if(AA[h] == 1)
			{
			printf("{ %u",h+1);   
			break;
			}
		for(i = h + 1; i < NumFilled; i++) if(AA[i] == 1) printf(", %u",i+1);
		printf(" }");
    	}
    	    
    if(Num_Pseudo_Min)
        {
        printf("\n\nPresentations which are Pseudo-Minimal:    ");
        for(h = 0; h < NumFilled; h++) if(AA[h] == 2)
            {
            printf("{ %u",h+1);   
            break;
            }
        for(i = h + 1; i < NumFilled; i++) if(AA[i] == 2) printf(", %u",i+1);
        printf(" }");       
        }
	
    if(Num_QPseudo_Min)
        {
        printf("\n\nPresentations which are QPseudo-Minimal:     ");
        for(h = 0; h < NumFilled; h++) if(AA[h] == 3)
            {
            printf("{%3d,",h+1);   
            break;
            }
        for(i = h + 1; i < NumFilled; i++) if(AA[i] == 3) if(++k < Num_QPseudo_Min) printf(", %u",i+1);
        printf(" }"); 
        }
    
    
    printf("\n\nTotal presentations with no separating pairs of vertices:  %u",NumFilled - Num_Bad_Diagrams);
    printf("\n\nTotal presentations not Pseudo-Minimal or QPseudo_Minimal and without separating pairs of vertices:  %u",
    	NumFilled - Num_Bad_Diagrams - Num_Pseudo_Min - Num_QPseudo_Min);
    printf("\n\nTotal Pseudo-Minimal presentations:  %u",Num_Pseudo_Min);
    printf("\n\nTotal QPseudo-Minimal presentations:  %u",Num_QPseudo_Min);
         
		printf("\n\nScroll back if necessary to see these lists.");    
	
		printf("\n\nPLEASE SELECT ONE OF THE FOLLOWING ALTERNATIVES."); 
		printf("\n    0) Show no presentations in the orbit.");
		printf("\n    1) Show only presentations which have no separating pairs of vertices.");
		printf("\n    2) Show only presentations which are Pseudo-Minimal."); 
		printf("\n    3) Show only presentations which are QPseudo_Minimal.");
		printf("\n    4) Show only presentations without Sep_Verts that are not Pseudo_Minimal or QPseudo_Minimal.");
		printf("\n    5) Show all presentations in the orbit.");
		printf("\nHIT 0,1,2,3,4, OR 5.    ");
		GET_RESPONSE4:   
		switch(WaitkbHit())
			{
			case '0':
				break;
			case '1':
				if(Num_Bad_Diagrams < NumFilled) 
					{
					printf("\n");
					for(i = 0; i < NumFilled; i++) 
					if(AA[i] > 0) 
						{
						printf("\nP %u)",i+1);
						Print_Relators(SUR[i],NR[i]);
						}
					}
				break;
			case '2':
				if(Num_Pseudo_Min) 
					{
					printf("\n");
					for(i = 0; i < NumFilled; i++) 
					if(AA[i] == 2) 
						{
						printf("\nP %u)",i+1);
						Print_Relators(SUR[i],NR[i]);
						}
					}
				break;
			case '3':
				if(Num_QPseudo_Min) 
					{
					printf("\n");
					for(i = 0; i < NumFilled; i++) 
					if(AA[i] == 3) 
						{
						printf("\nP %u)",i+1);
						Print_Relators(SUR[i],NR[i]);
						}
					}
				break;
			case '4':
				if(NumFilled > Num_Bad_Diagrams + Num_Pseudo_Min + Num_QPseudo_Min)
					{
					printf("\n");
					for(i = 0; i < NumFilled; i++) 
					if(AA[i] == 1) 
						{
						printf("\nP %u)",i+1);
						Print_Relators(SUR[i],NR[i]);
						}
					}
				break;
			case '5':
				printf("\n");
				for(i = 0; i < NumFilled; i++) 
					{
					printf("\nP %u)",i+1);
					Print_Relators(SUR[i],NR[i]);
					}
				break;	
			default:
				if(Batch == FALSE) SysBeep(5);
				goto GET_RESPONSE4;                    
			}
END:			        
    DisposePtr((unsigned char*) AA);              
}

unsigned int In_File(void)
{    
    unsigned char  	*p,
    				*q,
    				*r;
                            
    int           	i,
    				Result;
    
    unsigned int  	Node;
    
    Size          	HSP,
    				HSQ;     
    
    Canonical_Rewrite(Relators,FALSE,FALSE);
    Node = 0;
    while(1)
        {
        for(i = 1,Result = 0; i <= NumRelators; i++)
            {
            HSP = LR[i] + 1;
            HSQ = GetHandleSize((char **) SUR[Node][i]);
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
            r = *Relators[i] + LR[i];
            *r = 125;
            for(p = *Relators[i],q = *SUR[Node][i];    *p == *q; p++,q++) ;
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
                    if(Compute_Stabilizers)
                         printf("  %d -> %d",ReadPres + 1,NumFilled + 1);
                    if(Save_Pres(ReadPres,0,Length,1,75,0,3,0)) return(TOO_LONG);
                    UDV[NumFilled - 1] = 0;
                    BDY[NumFilled - 1] = BDY[ReadPres];
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
                SURNumX[Node] ++;     
                return(Node);
            case -1:
                if(Right[Node] == INFINITE)
                    {
                    if(Compute_Stabilizers)
                         printf("  %d -> %d",ReadPres + 1,NumFilled + 1);
                    if(Save_Pres(ReadPres,0,Length,1,75,0,3,0)) return(TOO_LONG);
                    UDV[NumFilled - 1] = 0;
                    BDY[NumFilled - 1] = BDY[ReadPres];
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