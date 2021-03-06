#include "Heegaard.h"
#include "Heegaard_Dec.h"

/****************************** Functions in Heegaard3.c ************************************
L 1376 Check_Bridge_Interlacing(unsigned int NumComps,unsigned int length)
L  140 Check_Connected(void)
L  540 Connected_(unsigned int i,unsigned int k)
L 1982 Diagram_Data(int PrintOut,int F1,int F2,Pres,HS)
L 2215 Diagram_Data_for_Graphviz(int F2,int Pres,int HS)
L 1670 Find_Cut_Vertices(void)
L 1281 Find_Minimal_Path(void)
L 2386 Gauss_Seidel(void)
L   86 Get_Matrix(void)
L  881 Planar(int Flag,int SaveFaces)
L 1330 Planar_Connected_(unsigned int length)
L 2676 Print_Bdry_Comp_Info(int F2,int Pres,int HS)
L 1744 Print_Graph(int F1,int F2,int Pres,int HS)
L  616 Sep_Pairs(int VI,int VJ,int FirstCall)
L  772 Sep_Pairs_Sub(v1,v2)
L  575 Split_Relators(unsigned char x)
L   27 Whitehead_Graph(void)
********************************************************************************************/

/*  #define PRINT_CYCLES    					*/				
/*  #define PRINT_TRIAL_CYCLES    				*/					
                            
unsigned int Whitehead_Graph(void)
{
    int     i;
    
    /******************************************************************************************
            Call Get_Matrix() to determine the valences of the vertices of the "reduced"
            Whitehead graph, and then delete extraneous components if the "reduced"
            Whitehead graph is not connected.
    ******************************************************************************************/    
    
    i = Get_Matrix();
    if(i == FALSE || (i == TRUE && !Connected) || (i == TRUE && MajorVert == 2))    
        {
        if(SPM_Flag && Check_Connected() == NOT_CONNECTED) return(NOT_CONNECTED);
        Saved_Vertices = Vertices;
        if(Check_Connected() == FALSE)
            {
            if(NotConnectedError == TOO_LONG)
                return(TOO_LONG);
            if(NotConnectedError == TOO_MANY_COMPONENTS)
                return(TOO_MANY_COMPONENTS);
            if(NotConnectedError)    
                return(REDUCE_GENUS);
            else
                return(NOT_CONNECTED);
            }
            
        /**************************************************************************************
            Next, call Sep_Pairs() to find out if there are any pairs of vertices whose removal
            gives a non-trivial separation of the "reduced" Whitehead graph.
        **************************************************************************************/
                
        SepPairs = Sep_Pairs(0,0,1);
        switch(SepPairs)
            {
            case 0:
                break;
            case 1:
                return(SEP_PAIRS);
            case TOO_LONG:
                return(TOO_LONG);
            }
                    
        /**************************************************************************************
            We now have a graph which is 3-connected. Call Planar(TRUE,FALSE) to determine
            whether this graph is planar.
        **************************************************************************************/ 
           
        NonPlanar = Planar(TRUE,FALSE);                
        if(NonPlanar) return(NON_PLANAR);
        }
	else
		{
		if(SepPairs)     return(SEP_PAIRS);
		if(NonPlanar)    return(NON_PLANAR);
		}                     
    return(Diagram_Main());                                                            
}    

int Get_Matrix(void)
{
    int    			i,
            		j,
            		k;
                    
    unsigned int    *Temp;
    
    /****************************************************************************************** 
            Set VWG[i] equal to the valence of vertex i in the "reduced" Whitehead graph. 
            Set NumEdges equal to the number of edges in the "reduced" Whitehead graph.
    ******************************************************************************************/
    
    for(i = NumEdges = 0;i < Vertices; i++)
        {
        A[i][i] = 0;
        for(j = k = 0; j < Vertices; j ++) if(A[i][j])
            {
            AJ2[i][k] = j;
            k++;
            }
        VWG[i] = k;
        NumEdges += k;
        AJ2[i][k] = VERTICES;
        }                            
    NumEdges /= 2;
    
    /******************************************************************************************
        Compare the adjacency matrices AJ1 and AJ2. If they are identical and Saved_Vertices
        equals Vertices return TRUE.
        Otherwise swap the arrays AJ1 and AJ2 and return FALSE.
    ******************************************************************************************/
    
    for(i = 0; i < Vertices; i++)
        {
        for(j = 0; ; j++)
            {
            if(AJ1[i][j] != AJ2[i][j])
                {
                for(i = 0; i < Vertices; i ++)
                    {
                    Temp = AJ1[i];
                    AJ1[i] = AJ2[i];
                    AJ2[i] = Temp;
                    }
                return(FALSE);
                }
            if(AJ2[i][j] == VERTICES) break;
            }
        }
    if(Saved_Vertices != Vertices || SPM_Flag) return(FALSE);            
    return(TRUE);        
}  
        
int Check_Connected(void)
{    
    unsigned char  	*p,
                    *q,
                    *r,
                    **Temp,
                    x;
                            
    int            	h,
    				i,
                    j;
    
    unsigned int    SaveUDV;
    
    unsigned long	HS;
        
    /****************************************************************************************** 
                    Check whether the "reduced" Whitehead graph is connected. 
    ******************************************************************************************/    
    
    for(i = 0; i < Vertices; i++) ZZ[i] = 0;
    Connected = Connected_(0,0); 
    if(Connected == FALSE && SPM_Flag) return(NOT_CONNECTED);   
    if(DrawingDiagrams == TRUE) return(TRUE);
    
    /****************************************************************************************** 
        If Connected is FALSE, then the "reduced" Whitehead graph is not connected, hence the 
        Heegaard diagram is reducible. So we call Split_Relators() to "split" the relators into
        two subsets corresponding to this splitting of the Heegaard diagram. 
    ******************************************************************************************/    
        
    if(Connected == FALSE)
        {
        if(Do_Not_Reduce_Genus)
        	{       	
        	UDV[ReadPres] = NOT_CONNECTED;
        	NotConnectedError = FALSE;
        	return(Connected);       	
        	}
        NotConnectedError = FALSE;    

        /**************************************************************************************
                If there are more than two generators and more than one relator, call
            Delete_Trivial_Generators(TRUE) to see if there are trivial generators which can
            be removed. If we are testing realizability, then we just check whether there are
            any trivial generators which can be deleted.
        **************************************************************************************/
        
        if(NumGenerators > 2 && NumRelators > 1 && !Do_Not_Reduce_Genus)
            {
            if(TestRealizability1 || TestRealizability2)
                h = Delete_Trivial_Generators(TRUE);
            else
                h = Delete_Trivial_Generators(FALSE);    
            switch(h)
                {
                case 0:
                    break;
                case 1:
                    NotConnectedError = TRUE;                                    
                    return(FALSE);
                case TOO_LONG:
                    NotConnectedError = TOO_LONG;
                    return(FALSE);    
                }
            }
            
        /**************************************************************************************
            Check whether the presentation that is "splitting" is already on file, if it is,
            we don't want to save another copy of it.
        **************************************************************************************/    
        
        SaveUDV = UDV[ReadPres];
        Canonical_Rewrite(Relators,FALSE,FALSE);        

        for(i = 0; i < NumFilled; i++)
		if(ComponentNum[i] == CurrentComp && SURL[i] == Length && NG[i] == NumGenerators && NR[i] == NumRelators)
			{
			 for(j = 1; j <= NumRelators; j++)
				 if(GetHandleSize((char **) Relators[j]) != GetHandleSize((char **) SUR[i][j])) break;
			 if(j > NumRelators && Compare_Pres(i)) 
			 	{
			 	if(i != ReadPres)
			 		{
			 		NotConnectedError = FALSE;
			 		return(FALSE);
			 		}
			 	break;
			 	}    
			 }
 
        if(i < NumFilled) switch(SaveUDV)
            {
            case SPLIT:
            case ANNULUS_EXISTS:
            case V2_ANNULUS_EXISTS:
                NotConnectedError = FALSE;
                return(FALSE);
            }
                                         
        /**************************************************************************************
                Since we have rewritten the relators, we need to update the relevant arrays.
        **************************************************************************************/    
        
        Fill_A(NumRelators);
        Get_Matrix();
        for(j = 0; j < Vertices; j++) ZZ[j] = 0;
        Connected_(0,0);

        if(Micro_Print == 1)
            {
            printf("\n\nThe diagram of the following presentation from Presentation %d is not connected.\n",
                ReadPres + 1);
            Print_Relators(Relators,NumRelators);
            }
            
        if(i == NumFilled)
            {
            /**********************************************************************************
                The presentation that is "splitting" is new, so we want to save a copy.
            **********************************************************************************/
            
            /**********************************************************************************
                If Whitehead_Graph() was called by Lens_Space(), we want to check whether the
                presentation of the "lens-space" is the standard presentation of the 3-Sphere
                at this point. If we don't do this, Heegaard will eventually discover that
                it has the 3-Sphere, but only after producing some redundant presentations and
                diagrams.
            **********************************************************************************/
            
            if(Length == NumGenerators && NumRelators == NumGenerators && !Boundary)
                {
                for(i = 1; i <= NumRelators; i++) if(GetHandleSize((char **) Relators[i]) != 2) break;
                if(i > NumRelators && Delete_Dups() == NumRelators)
                    {
                    if(Micro_Print == 1)
                        printf("\n\nThe current presentation presents the 3-Sphere.");
                    if((NumFilled >= MAX_SAVED_PRES - 3) || 
                        Save_Pres(ReadPres,0,Length,1,5,0,0,0))
                        {
                        NotConnectedError = TOO_LONG;
                        return(FALSE);
                        }        
                    BDY[NumFilled - 1] = BDY[ReadPres];
                    UDV[NumFilled - 1] = THREE_SPHERE;
                    if(CBC[CurrentComp][0] == BDRY_UNKNOWN)
                        {
                        CBC[CurrentComp][0] = 1;
                        CBC[CurrentComp][1] = BDRY_UNKNOWN;
                        }
                    Mark_As_Found_Elsewhere(CurrentComp);
                    }
                return(FALSE);    
                }
                    
            if((NumFilled >= MAX_SAVED_PRES - 3) ||Save_Pres(ReadPres,0,Length,1,20,1,0,0))
                {
                NotConnectedError = TOO_LONG;
                return(FALSE);
                }
            BDY[NumFilled - 1] = BDY[ReadPres];
            UDV[NumFilled - 1] = 0;            
            SaveUDV = 0;
            ReadPres = NumFilled - 1;
            }
            
        /**************************************************************************************
             If Heegaard already has as many summands as it can handle, flag any other
             presentations corresponding to this summand so that we will quit processing them.
         **************************************************************************************/    
         
         if(TotalComp > MAXNUMCOMPONENTS - 3)
             {
            Mark_As_Found_Elsewhere(CurrentComp);    
            NotConnectedError = TOO_MANY_COMPONENTS;
            if(Batch == FALSE) SysBeep(5);
            printf("\n\nStopping because Heegaard cannot deal with any more summands. Sorry!"); 
            printf("\n\nRerunning using Depth-First Search may help.");
            if(NumErrors == 1)
				printf("\nOne error was detected. Scroll back for details.");
			if(NumErrors > 1)
				printf("\n%lu errors were detected. Scroll back for details.",NumErrors); 
			Too_Many_Components_ALert(); 
            return(FALSE);
            }
                         
        /**************************************************************************************
            Call Split_Relators() to partition the relators into two subsets. One subset will
            consist of those relators which contain generators corresponding to vertices
            occuring in the component of the Whitehead graph containing vertex number zero, 
            while the other subset will consist of the remaining relators.
        **************************************************************************************/
                
        for(i = NumDelRelators = 0; i < Vertices; i += 2) if(ZZ[i])
            {
            x = i/2 + 65;
            Split_Relators(x);                                        
            }
                                
        /**************************************************************************************
            Call Rewrite_Input() to rewrite the undeleted relators. Save the rewritten
            relators in SUR[]. Increase TotalComp by 1 and update Daughters[]. Then increase
            TotalComp by 1 more, and call Rewrite_Input() to rewrite the deleted relators.
            Save the rewritten deleted relators in SUR[].
        **************************************************************************************/
                
        Rewrite_Input();
        for(i = 1, Length = 0L; i <= NumRelators; i++)
            Length += GetHandleSize((char **) Relators[i]);
        Length -= NumRelators;
        if((DisAmbigFlag == TRUE) && (1 < NumGenerators) && (NumGenerators + 1 < NG[ReadPres])) CS[CurrentComp] = TRUE;
        if(DisAmbigFlag == FALSE) CS[CurrentComp] = TRUE;
        
        TotalComp                       ++;
        UDV[ReadPres]                   = SPLIT;
        NCS[ReadPres]                   = 2;                
        Daughters[ReadPres]            	= NumFilled;
        ComponentNum[NumFilled]         = TotalComp;        
        ER[NumFilled]                   = -3;
        FR[NumFilled]                   = ReadPres;        
        MLC[TotalComp][NumGenerators]   = Length;
        NG[NumFilled]                   = NumGenerators;
        NR[NumFilled]                   = NumRelators;
        PRIM[NumFilled]                 = 20;
        SURL[NumFilled]                 = Length;
        UDV[NumFilled]                  = 0;
        TP[NumFilled]                   = NumRelators;
        BDY[NumFilled]                  = BDY[ReadPres];
        OnStack                         += 2*NumGenerators;
        HegSplNum[NumFilled]			= NumFilled;
        HegSplNxt[NumFilled]			= NumFilled;
        if(NumGenerators == 1)
        	{
        	UDV[NumFilled] = GENERIC_LENS_SPACE;
        	LSP[NumFilled] = GetHandleSize((char **) Relators[1]) - 1;
        	LSQ[NumFilled] = 1;
        	}

 		if(CS[ComponentNum[ReadPres]] == TRUE) for(i = 0; i < NumFilled; i++) 
 			if(ComponentNum[i] == ComponentNum[ReadPres] && UDV[i] < DONE) UDV[i] = DONE;
 	           
        Canonical_Rewrite(Relators,FALSE,FALSE);
        
        for(i = 1; i <= NumRelators; i++)
            {
            HS = GetHandleSize((char **) Relators[i]);
            if(SUR[NumFilled][i] != NULL) DisposeHandle((char **) SUR[NumFilled][i]);
            SUR[NumFilled][i] = (unsigned char **) NewHandle(HS);            
            if(SUR[NumFilled][i] == NULL) Mem_Error();
            p = *Relators[i];           
            q = *SUR[NumFilled][i];    
	    	r = q;
	   	 	while( (*q++ = *p++) ) ;
	    	}
            
        BytesUsed += Length;        

        for(i = 0; i < NumFilled; i++)
            if(SURL[i] == Length  
                && NG[i] == NumGenerators
                && NR[i] == NumRelators)
            {
             for(j = 1; j <= NumRelators; j++)
                 if(GetHandleSize((char **) Relators[j]) != GetHandleSize((char **) SUR[i][j])) break;    
             if(j > NumRelators && Compare_Pres(i))
                 {
                 Daughters[NumFilled] = i;
                 if(CBC[ComponentNum[i]][0] != BDRY_UNKNOWN)
                     {
                     h = ComponentNum[i];
                     for(j = 0; (CBC[TotalComp][j] = CBC[h][j]) < BDRY_UNKNOWN; j++) ;
                     }
                 break;
                 }    
             }
                                                                 
        NumFilled ++;
        SaveMinima = TRUE;
        
        if(Micro_Print == 1)
            {
            printf("\nThe presentation of the first summand is:\n");
            Print_Relators(Relators,NumRelators);
            printf("\n\nSaved this presentation as: Presentation %u\n",NumFilled);
            }
                
        printf("\nPres%6u  ToDo%7u  Summand%3d  ",NumFilled,OnStack,TotalComp);
        printf("Gen%3d  Rel%3d  Length%6lu  From%6d  NC",
            NumGenerators,NumRelators,Length,ReadPres + 1);
        
        NumRelators = NumDelRelators;
        
        for(i = 1; i <= NumRelators; i++)
            {
            Temp = Relators[i];
            Relators[i] = DelRelators[i];
            DelRelators[i] = Temp;
            }
        
        Rewrite_Input();
        
        for(i = 1, Length = 0L; i <= NumRelators; i++)
            Length += GetHandleSize((char **) Relators[i]);
        Length -= NumRelators;
        
        TotalComp                       ++;
        ComponentNum[NumFilled]         = TotalComp;    
        ER[NumFilled]                   = -3;
        FR[NumFilled]                   = ReadPres;    
        MLC[TotalComp][NumGenerators]   = Length;
        NG[NumFilled]                   = NumGenerators;
        NR[NumFilled]                   = NumRelators;
        PRIM[NumFilled]                 = 20;    
        SURL[NumFilled]                 = Length;
        UDV[NumFilled]                  = 0;
        TP[NumFilled]                   = NumRelators;
        BDY[NumFilled]                  = BDY[ReadPres];
        OnStack                         += 2*NumGenerators;
        HegSplNum[NumFilled]			= NumFilled;
        HegSplNxt[NumFilled]			= NumFilled;
        if(NumGenerators == 1)
        	{
        	UDV[NumFilled] = GENERIC_LENS_SPACE;
        	LSP[NumFilled] = Length;
        	LSQ[NumFilled] = 1;
        	}
        	        
        Canonical_Rewrite(Relators,FALSE,FALSE);
        
        for(i = 1; i <= NumRelators; i++)
            {
            HS = GetHandleSize((char **) Relators[i]);
            if(SUR[NumFilled][i] != NULL) DisposeHandle((char **) SUR[NumFilled][i]);
            SUR[NumFilled][i] = (unsigned char **) NewHandle(HS);            
            if(SUR[NumFilled][i] == NULL) Mem_Error();
            p = *Relators[i];            
            q = *SUR[NumFilled][i]; 
            r = q;   
            while( (*q++ = *p++) ) ;            
            }
        
        BytesUsed += Length;
            
        for(i = 0; i < NumFilled; i++)
            if(SURL[i] == Length  
                && NG[i] == NumGenerators
                && NR[i] == NumRelators)
            {
             for(j = 1; j <= NumRelators; j++)
                 if(GetHandleSize((char **) Relators[j]) != GetHandleSize((char **) SUR[i][j])) break;    
             if(j > NumRelators && Compare_Pres(i))
                 {
                 Daughters[NumFilled] = i;
                 if(CBC[ComponentNum[i]][0] != BDRY_UNKNOWN)
                     {
                     h = ComponentNum[i];
                     for(j = 0; (CBC[TotalComp][j] = CBC[h][j]) < BDRY_UNKNOWN; j++) ;
                     }    
                 break;
                 }    
             }
                                                         
        NumFilled ++;
        SaveMinima = TRUE;
        
        if(Micro_Print == 1)
            {
            printf("\nThe presentation of the second summand is:\n");
            Print_Relators(Relators,NumRelators);
            printf("\n\nSaved this presentation as: Presentation %u\n",NumFilled);
            }        
        
        if(BDY[ReadPres] == FALSE)
            {
            if(CBC[TotalComp - 1][0] == BDRY_UNKNOWN)
                {
                CBC[TotalComp - 1][0] = 1;
                CBC[TotalComp - 1][1] = BDRY_UNKNOWN;
                }
            if(CBC[TotalComp][0] == BDRY_UNKNOWN)
                {
                CBC[TotalComp][0] = 1;
                CBC[TotalComp][1] = BDRY_UNKNOWN;
                }    
            }
            
        for(i = 1; i <= NumDelRelators; i++) if(DelRelators[i] != NULL) 
        	{
        	DisposeHandle((char **) DelRelators[i]);
        	DelRelators[i] = NULL;
        	}
        NumDelRelators = 0;
                        
        printf("\nPres%6u  ToDo%7u  Summand%3d  ",NumFilled,OnStack,TotalComp);
        printf("Gen%3d  Rel%3d  Length%6lu  From%6d  NC",
            NumGenerators,NumRelators,Length,ReadPres + 1);            
        }
    return(Connected);                
}    

int Connected_(unsigned int i,unsigned int k)
{    
    /******************************************************************************************
        This routine finds those vertices in the component of vertex i in the graph specified
        in the adjacency lists AJ1[]. The array ZZ[] is initialized by the calling routine
        which sets the entries of vertices which should be deleted from the adjacency lists to
        a non-zero value and passes the number of deleted vertices as the parameter k. 
        The routine returns FALSE if the graph is not connected, returns TRUE if the graph is
        connected, and sets ZZ[j] = 1 if j lies in the component of the graph containing i. 
    ******************************************************************************************/    
     
    unsigned int   	h,
    				j,
    				*p,
    				*r;
    				                                                     
    ZZ[i] = 1;
    k ++;
    for(r = UpDate,*r = i,p = r + 1; r < p; r++)
        {
        i = *r;
        for(h = 0; (j = AJ1[i][h]) < VERTICES; h++)
            {
            if(ZZ[j] == 0)
                {
                ZZ[j] = 1;
                *p++ = j;
                if(++k == Vertices) return(TRUE);
                }
            }
        }            
    if(k < Vertices) return(FALSE);        
    return(TRUE);        
}                                

void Split_Relators(unsigned char x)
{
    /******************************************************************************************
        This routine searches through the relators in Relators[] looking for relators that
        contain the specified character x or its inverse. Any relator that contains x or its
        inverse is removed from the set of relators and saved in the array DelRelators[].
    ******************************************************************************************/
        
    unsigned char   *p,
    				**Temp,
                    y,
                    z;
                            
    int             i;
    
    y = x + 32;
    for(i = 1; i <= NumRelators; i++)
        { 
        if(GetHandleSize((char **) Relators[i]) > 1)
            {
            p = *Relators[i];
            while( (z = *p++) )
                {
                if((z == x) || (z == y))
                    {
                    Temp = DelRelators[NumDelRelators + 1];
                    DelRelators[NumDelRelators + 1] = Relators[i];
                    Relators[i] = Temp;
                    if(Relators[i] != NULL) DisposeHandle((char **) Relators[i]);
                    Relators[i] = (unsigned char **) NewHandle(sizeof(char));
                    if(Relators[i] == NULL) Mem_Error();
                    p = *Relators[i];
                    *p = EOS;        
                    NumDelRelators++;
                    break;
                    }    
                }    
            }
        }    
}

int Sep_Pairs(int VI,int VJ,int FirstCall)
{    
    /******************************************************************************************
        This routine determines whether the graph specified by the adjacency lists in AJ1[],
        has a separating pair of vertices. It deletes, in turn, each vertex, of valence greater
        than two, from the graph and then uses a stack-based version of depth-first-search to
        determine if the resulting graph has a separating vertex. The routine returns TRUE if
        it finds a pair of vertices which "essentially" separates the graph and otherwise
        returns FALSE. If the original graph has more than two major vertices, the routine
        calls Sep_Pairs_Sub() which sets the globals V1 and V2 to the first separating pair of 
        vertices (V1,V2), which follow the ordered pair (VI,VJ) in lexicographic order. 
        Otherwise, it sets the globals V1 and V2 to the ordered pair of major vertices. 
    ******************************************************************************************/
    
    unsigned int   	i,
                	j,
                    k,
                    K,
                    m,
                    *p;
    
    unsigned int    VG[VERTICES],
                    root;
                                   
    if(FirstCall)
    	{
		/**************************************************************************************
			Count the number of vertices of the graph which have valence greater than two,
			and deal with the special case where there are exactly two of these.
		**************************************************************************************/
		
		for(m = MajorVert = 0; m < Vertices; m++)
			if(VWG[m] > 2)
				{
				MajorVert++;
				if(MajorVert == 1)
					i = m;
				else
					{    
					if(MajorVert == 2)
						j = m;
					else
						break;
					}
				} 
				
		if(MajorVert == 2)
			{
			/**********************************************************************************    
				The graph has exactly two major vertices given by the values of i and j.
				If the valence of vertex i is greater than 3 or there is more than one edge 
				joining vertex i and j then the graph does not have a unique planar embedding.
			**********************************************************************************/    
							
			if((VWG[i] > 3) || (A[i][j] > 1))
				{ 
				V1 = i;
				V2 = j;
				NumComps = VWG[i];
				return(TRUE);
				}
			else
				{
				V1 = i;
				V2 = j;
				return(FALSE);                                                    
				}                
			}
        }
        
    /******************************************************************************************
        If we are here, the graph has more than two major vertices, and we go into the main
        loop of the routine.
    ******************************************************************************************/
                            
    for(i = VI; i < Vertices - 1; i ++)
        {
        if(VWG[i] < 3) continue;
        
        for(j = 0; j < Vertices; j++) Number[j] = 0;
        if(i == 0)
            root = 1;
        else
            root = 0;
        Lowpt[i]         = 0;        
        Father[i]        = i;
        NumVert          = 1;
        Number[root]     = 1;
        Lowpt[root]      = 1;
        Father[root]     = root;
        VG[root]         = 0;
        for(p = UpDate,*p = root; p >= UpDate; p--)
            {
            NEW_VERT:
            m = *p;
            for(k = VG[m]; (j = AJ1[m][k]) < VERTICES; k++)
                {
                if(j == i) continue;
                if(Number[j] == 0)
                    {
                    NumVert       ++;
                    Number[j]     = NumVert;
                    Lowpt[j]      = NumVert;
                    Father[j]     = m;
                    VG[j]         = 0;
                    VG[m]         = k + 1;
                    p             ++;
                    *p            = j;
                    goto         NEW_VERT;        
                    }
                if(j != Father[m] && Number[j] < Lowpt[m])
                    Lowpt[m] = Number[j];        
                }
            if(Lowpt[m] < Lowpt[Father[m]]) Lowpt[Father[m]] = Lowpt[m];    
            }

        if(i == 0 && VJ == 0 && root == 1 && VWG[root] >= 3)
            {
            /**********************************************************************************
                Check whether the root of the depth-first-search tree is a cut vertex. This 
                will be the case iff the root has more than one son.
            **********************************************************************************/
        
            for(m = k = 0; (j = AJ1[root][m]) < VERTICES; m++)
                if(Father[j] == root && ++k > 1) break;
            
            if(k > 1 && Sep_Pairs_Sub(i,root)) return(TRUE);
            
            /**********************************************************************************
                If k > 1, the root of the depth-first-search tree is a cut vertex.
                Otherwise, we look for other cut vertices.
            **********************************************************************************/
            
            }

        for(j = 0,K = VERTICES; j < Vertices; j ++)
            {
            k = Father[j];
            if(VWG[k] < 3) continue;
            if(i == VI && k <= VJ) continue;
            if(i != VI && k <= i) continue;
            if(k >= K) continue;                        
            if(Lowpt[j] >= Number[k] && k != root && Sep_Pairs_Sub(i,k))
                K = k;
            }
        if(K < VERTICES) return(TRUE);        
        }    
        
    /******************************************************************************************
        We have checked each pair of distinct major vertices of the graph without finding a
                            pair which produced a proper separation.
    ******************************************************************************************/
                                                        
    return(FALSE);    
}

int Sep_Pairs_Sub(v1,v2)
{
    /******************************************************************************************
        We have found a pair of distinct vertices v1 and v2 which separate the graph and both
        v1 and v2 have valence greater than two. Determine how many components arise when v1
        and v2 are deleted from the graph, and also determine if the components are such that
        the graph is not 3-connected. (See below for details.)
    ******************************************************************************************/
    
    int            	i,
                	j,
                    k,
                    m,
                    n;

    unsigned int    *p,
                    *r,
                    *zz;
    
    zz = ZZ;
    for(k = 0; k < Vertices; k++) zz[k] = 0;
    zz[v1] = zz[v2] = VERTICES;
    for(k = 0; (k < Vertices) && zz[k]; k++) ;
    
    p            = UpDate;
    *p++         = k;
    zz[k]        = 1;
    k            = 3;
    NumComps     = 1;
    while(1)
        {                
        for(r = UpDate; r < p; r++)
            {
            i = *r;
            for(m = 0; (j = AJ1[i][m]) < VERTICES; m++)
                {
                if(zz[j] == 0)
                    {
                    zz[j] = NumComps;
                    *p++ = j;
                    if(++k >= Vertices) goto FOUND_COMPS;
                    }
                }
            }
        if(k >= Vertices) break;
        if(++NumComps > 2) break;
        for(m = 0, p = UpDate; m < Vertices; m++) if(!zz[m])
            {
            zz[m] = NumComps;
            k++;
            *p++ = m;
            break;
            }    
        }
        
FOUND_COMPS:
    
    i = v1;
    j = v2;
    
    /******************************************************************************************
        If removing the vertices i and j produced a graph with more than two components, or a
        graph with two components and vertices i and j are joined by an edge, then the graph
        is not 3-connected. (In the 2-component case, at least one component contains a
        major vertex.)
    ******************************************************************************************/    
            
    if((NumComps >= 3) || ((NumComps == 2) && A[i][j]))
        {
        V1 = i; 
        V2 = j;
        return(TRUE);
        }
        
    /******************************************************************************************
        If execution gets to this point, the graph has two components and vertices i and j are
        not joined by an edge. Check whether each component contains a vertex with valence
        greater than two. If so, the graph is not 3-connected.
    ******************************************************************************************/
        
    for(m = 0,k = FALSE,n = -1; m < Vertices; m++)
        {
        if(m == i || m == j) continue; 
        if(VWG[m] > 2)
            {
            if(n < 0) n = zz[m];
            if(n != zz[m])
                {
                k = TRUE;
                break;
                }
            }    
        }
        
    /******************************************************************************************
                If k is TRUE, each component of the graph contains a vertex with valence
                greater than two and the graph is not 3-connected.
    ******************************************************************************************/
            
    if(k)
        {
        V1 = i;
        V2 = j;
        return(TRUE);
        }
        
    return(FALSE);            
}

int Planar(int Flag,int SaveFaces)
{
    /******************************************************************************************
        This routine determines whether the graph specified by the set of adjacency lists
        AJ1[i][] is planar. It also locates a cycle of vertices which will be the boundary of
        the "infinite" face of the graph. It returns FALSE if the graph is planar and TRUE if
        the graph is nonplanar.
    ******************************************************************************************/
	
    int             Bdry_Major_Vert,
    				h,
    				i,
    				ii,
    				j,
    				jj,
    				k,			
                    Max_Bdry_Major_Vert,
                    MaxNumFaces,
                    NumInPS,
                    P1,
                    P2,
                    s1,
                    s2,
                    V;
                                        
    unsigned int   	InitialVertex,
    				*MyBdry,
                    *q,
                    length;
                            
    /******************************************************************************************
        First take care of the special case where the number of vertices is less than or equal
        to two. 
        Next, if the graph has more than 3(Vertices - 2) edges, return TRUE, since the graph
        is nonplanar.
    ******************************************************************************************/
                            
    if(Vertices <= 2)
        {
        FV[0] = 1;
        FV[1] = 0;
        CO[0][1] = 1;
        CO[1][0] = 0;
        NumFaces = 1;
        MaxLength = 1;
        return(FALSE);
        }        
    if(NumEdges > 3*(Vertices - 2)) return(TRUE);
 
	ii = 0;
	jj = 0;
	InitialVertex		= VERTICES;                                                                                                                                    
    MaxLength           = VERTICES + 1;
    NumFaces            = 0;
    Max_Bdry_Major_Vert = -1;
    MaxNumFaces         = NumEdges - Vertices + 2;
    for(h = 0; h < Vertices; h++)
    for(i = 0; i < Vertices; i++) GB[h][i] = FALSE;
    for(i = 0; i < Vertices; i++)
    for(q = AJ1[i]; (j = *q) < VERTICES; q++) GB[i][j] = TRUE;
    for(i = 0; i < Vertices; i++) InPS[i] = FALSE;  	
            
    /******************************************************************************************
        Find an oriented edge of the graph to serve as the first edge of the boundary of the
        initial face of the graph. Then delete the oppositely oriented edge from the array
        GB[][] so that the path-finding routine, Find_Minimal_Path(), will not return with a
        minimal path which yields a degenerate cycle. Planar() now works essentially by 
        adjoining faces one-by-one to a planar surface yielding a new planar surface which
        eventually contains all of the faces of the graph -- provided the graph is planar.
        Note that Planar() works whether or not the graph has separating pairs of vertices.
    ******************************************************************************************/

	i 					  = ii;  
    j                     = AJ1[i][jj];
    MyBdry                = Bdry;
    MyBdry[0]             = i;
    MyBdry[1]             = j;
    GB[j][i]              = FALSE;
    DeletedEdgePtr        = DeletedEdges;
    *DeletedEdgePtr++     = j;
    *DeletedEdgePtr++     = i;    
  	InPS[i]               = 1;
    InPS[j]               = 1;
    NumInPS               = 2;    
    s1                    = 0;
    s2                    = 0;
    
FIND_BDRY:

    length = Find_Minimal_Path();
    
    /**********************************************************************************************
    	If Find_Minimal_Path() returns a circuit P which contains all of the vertices currently
    	in InPS, then there are no vertices in the interior of the current planar surface. In
    	order to avoid a possible erroneous declaration that P bounds a face, we look for a
    	vertex V of P which can be isolated so that Heegaard will find a new path P' with V not
    	contained in P'. To do this, we first choose a vertex V' not in P, find the component C
    	of the graph G-P containing V' and locate the first P1 and second point P2 at which C 
    	meets P. Then V can be taken to be any vertex not in the oriented path from P1 to P2 in P.
    ***********************************************************************************************/
    
    if(length + 1 == NumInPS && NumInPS < Vertices)
    	{   	
    	for(h = 0; h <= length && InPS[Bdry[h]] == 1; h++) {}
    	if(h >= NumInPS)
    		{
           	while(DeletedEdgePtr > DeletedEdges)
				{
				DeletedEdgePtr --;
				j = *DeletedEdgePtr --;
				GB[*DeletedEdgePtr][j] = TRUE;
				}       	 	
       	 	length ++;		
 			for(i = 0; i < Vertices; i++)
 				{ 
 				if(InPS[i]) ZZ[i] = VERTICES;
 				else ZZ[i] = 0;
 				}
 			for(i = 0; i < Vertices; i++) if(InPS[i] == FALSE) break;
 			Connected_(i,NumInPS);	
 			for(i = 1,P1 = 0; i <= length; i++)
				{
				for(q = AJ1[Bdry[i]]; (j = *q) < VERTICES; q++)
					{
					if(ZZ[j] == 1)
						{
						P1 = i;
						break;
						}                
					}
				if(P1) break;	
				}
			for(i = P1 + 1,P2 = 0; i <= length; i++)
				{
				for(q = AJ1[Bdry[i]]; (j = *q) < VERTICES; q++)
					{
					if(ZZ[j] == 1)
						{
						P2 = i;
						break;
						}                
					}
				if(P2) break;	
				}				
			if(P1 > 1)
				{
				V = Bdry[P1-1];
				Bdry[0] = Bdry[P1];
				Bdry[1] = Bdry[P1+1];
				}	
			if(P1 == 1 && P2 < length)
				{
				V = Bdry[P2+1];
				Bdry[0] = Bdry[1];
				Bdry[1] = Bdry[2];
				}
			if(P1 == 1 && P2 == length) 	
				{
				Bdry[0] = Bdry[length];
				Bdry[1] = Bdry[1];
				V = Bdry[2];
				}			
			for(j = 0; j < Vertices; j++) if(GB[j][V] == 1)
				{
				GB[j][V] = 0;
				*DeletedEdgePtr++ = j;
				*DeletedEdgePtr++ = V;
				}	
			s1 = s2 = 0;       		
        	length = Find_Minimal_Path();		
    		}
    	}
    
    if(length == 0)
        {               
        /**************************************************************************************
            There is no directed path joining Bdry[1] to Bdry[0]. This can only occur when the
            graph is not planar. So set NumFaces = MaxNumFaces + 1 as a flag, and goto OUTPUT.
        **************************************************************************************/ 
        NumFaces = MaxNumFaces + 1;
        goto OUTPUT;
        }

    /******************************************************************************************
        Heegaard has found a cycle of length at least three. See if removing the vertices
        of this cycle disconnects the graph.
    ******************************************************************************************/    
    
    #ifdef PRINT_TRIAL_CYCLES
		printf("\n\n Trial_Cycle = ");        
        for(k = 0; k <= length; k++)
            {
            h = MyBdry[k];
            if(h & 1)
                c = h/2 + 97;
            else
                c = h/2 + 65;    
            printf("%c",c);
            }
    #endif
        
    if(NumInPS < Vertices && (length + 1 < Vertices))
        { 
        for(h = 0; h < Vertices; h++) ZZ[h] = 0;	
        for(h = 0; h <= length; h++) ZZ[MyBdry[h]] = VERTICES;
        
        /***************************************************************************************
        	When Heegaard finds an initial circuit P and no faces have been found, we choose an
        	arbitrary vertex V not in P, and insist that V lie on the 'outside' of any 
        	subsequent paths Heegaard finds. This forces Heegaard to look for a sequence of
        	nested paths all of which have V lying to the same side.
        ***************************************************************************************/
        
        if(NumFaces == 0 && InitialVertex == VERTICES)
        	{
        	for(h = 0; h < Vertices; h++) if(ZZ[h] != VERTICES) break;
        	InitialVertex = h;
        	}
        if(NumFaces == 0) Connected_(InitialVertex,length + 1);
        k = Planar_Connected_(length + 1);
        if(k == NON_PLANAR)
        	{
        	NumFaces = MaxNumFaces + 1;
        	goto OUTPUT;        	
        	}
        }    
    else
        k = 1;
                                            
    if(k == 1)            
        {
        /**************************************************************************************
            Removing the vertices of the cycle does not disconnect the graph. Hence, it is a
            boundary of a face. Restore any edges which where deleted from GB[][] while looking
            for the boundary of this face. Then increment the number of faces.      
        **************************************************************************************/
        
        while(DeletedEdgePtr > DeletedEdges)
            {
            DeletedEdgePtr --;
            j = *DeletedEdgePtr --;
            GB[*DeletedEdgePtr][j] = TRUE;
            }
                  
        length   ++;                            
        NumFaces ++;
       
        /**************************************************************************************
            If Flag is FALSE, we intend to draw the graph. In this case,if the number of major
            vertices in this cycle is greater than the maximal number of major vertices in any
            previous cycle, we save this cycle in the array SaveBdry[]. Then, if the graph is
            planar, the boundary of the infinite face will contain the maximal possible number
            of major vertices and, subject to this constraint, as many vertices as possible.
        **************************************************************************************/
            
        if(Flag == FALSE)
            {
            for(Bdry_Major_Vert = h = 0; h < length; h++)
            if(VWG[MyBdry[h]] > 2) Bdry_Major_Vert ++;         
            if(Bdry_Major_Vert > Max_Bdry_Major_Vert)
                { 
                Max_Bdry_Major_Vert = Bdry_Major_Vert;
                MaxLength = length;
                for(k = 0;k < MaxLength; k++) SaveBdry[k] = MyBdry[k];    
                }
            else
            if(Bdry_Major_Vert == Max_Bdry_Major_Vert && length > MaxLength)
                { 
                MaxLength = length;
                for(k = 0;k < MaxLength; k++) SaveBdry[k] = MyBdry[k];    
                }                
            }
        
        if(SaveFaces)
            {
            for(k = 0; k < length; k++) Face[NumFaces][k] = MyBdry[k];
            Face[NumFaces][k] = VERTICES;    
            }
                        
      #ifdef PRINT_CYCLES
            printf("\n\n %d) ",NumFaces);
            for(k = 0; k < length; k++)
                {
                h = MyBdry[k];
                if(h & 1)
                    c = h/2 + 97;
                else
                    c = h/2 + 65;    
                printf("%c",c);
                }
            for( ; k < 26; k++)
                printf(".");    
            printf(" bounds.");
       #endif
                                                
        /**************************************************************************************
            For each oriented edge of this cycle, set the corresponding entry of GB[][] equal
            to -1. (If the graph is planar, each oriented edge will appear in the boundary of
            exactly one oriented face.) Then update the entries of the array CO[][]. This array
            gives the cyclic order in which vertices appear around a vertex in the embedding
            of the graph.
        **************************************************************************************/

        for(k = 0,h = MyBdry[length - 1]; k < length; k++)
            {
            j = MyBdry[k];
            GB[h][j] = -1;       
            h = j;
            if(!InPS[j])
                {
                InPS[j] = TRUE;
                NumInPS ++;
                }
            }              
        for(k = 0; k < length - 2; k++) CO[MyBdry[k+1]][MyBdry[k]] = MyBdry[k+2];
        CO[MyBdry[k+1]][MyBdry[k]] = MyBdry[0];
        CO[MyBdry[0]][MyBdry[k+1]] = MyBdry[1];
        
        /**************************************************************************************
            Look for an oriented edge, in the boundary of the current planar surface, which
            can serve as the first edge of the boundary of the next face. If no such edge
            exists, goto OUTPUT.
        **************************************************************************************/
            
        for(h = s1,i = s2; (j = AJ1[h][i]) < VERTICES; i++) if(GB[h][j] == 1)
            {
            s1 = h;
            s2 = i;
            goto FIND_FIRST_EDGE;
            }
        for(h = s1 + 1; h < Vertices; h++)
        for(i = 0; (j = AJ1[h][i]) < VERTICES; i++) if(GB[h][j] == 1)
            {
            s1 = h;
            s2 = i;
            goto FIND_FIRST_EDGE;
            }    
        FIND_FIRST_EDGE:
        
        for(h = s1,i = s2; (j = AJ1[h][i]) < VERTICES; i++) if(GB[h][j] == 1 && GB[j][h] != 1)
            {
            MyBdry[0] = h;
            MyBdry[1] = j;
            goto FIND_BDRY;
            }
        for(h = s1 + 1; h < Vertices; h++)
        for(i = 0; (j = AJ1[h][i]) < VERTICES; i++) if(GB[h][j] == 1 && GB[j][h] != 1)
            {
            MyBdry[0] = h;
            MyBdry[1] = j;
            goto FIND_BDRY;
            }
        goto OUTPUT;                                                        
        }
    
    goto FIND_BDRY;    
    
OUTPUT:
    if(MaxLength == Vertices || NumFaces == MaxNumFaces)
        {
        for(i = 0; i < Vertices; i++) if(VWG[i])
            FV[i] = AJ1[i][0];
            
        /**************************************************************************************
                FV[i] is the first vertex in the counterclockwise cyclic ordering of the
                                vertices joined to vertex i.
        **************************************************************************************/
        
        #ifdef PRINT_LINKS
            for(i = 0; i < Vertices; i++) if(VWG[i])
                {
                if(i & 1)
                    c = i/2 + 97;
                else
                    c = i/2 + 65;
                printf("\nThe vertices in cyclic order about vertex %c are: ",c);
                for(j = 0; j < Vertices; j++) if(A[i][j] && i != j) break;
                if(j & 1)
                    c = j/2 + 97;
                else
                    c = j/2 + 65;
                printf("%c",c);
                k = CO[i][j];
                while(k != j) 
                    {
                    if(k & 1)
                        c = k /2 + 97;
                    else
                        c = k/2 + 65; 
                    printf("%c",c);
                    k = CO[i][k];
                    }
                }
        #endif                
        return(FALSE);
        }            
    else      
        return(TRUE);                                                                  
}                

unsigned int Find_Minimal_Path(void)
{
    /******************************************************************************************
        Find_Minimal_Path() is called by Planar(). Find_Minimal_Path() finds a minimal length
        directed path, in the graph specified by GB[][], which joins the vertices Bdry[1] and
        Bdry[0]. The path is returned in the array Bdry[], while the value returned by the
        routine is equal to the length of the path. If no path can be found, the routine
        returns 0.
    ******************************************************************************************/
    
    char			FoundPath;
    
	unsigned int	h,
					i,
					MyUpDate[VERTICES],
					PathNext[VERTICES],
					*p,
					*r;
						
	for(h = 0; h < Vertices; h++) PathNext[h] = VERTICES;
	PathNext[Bdry[0]] = 0;
				
	p = MyUpDate;
	*p++ = Bdry[0];
	for(r = MyUpDate,FoundPath = FALSE; r < p; r++)
		{
		i = *r;
		for(h = 0; h < Vertices; h++) if(PathNext[h] == VERTICES && GB[h][i] == 1)
			{			
			PathNext[h] = i;
			if(h == Bdry[1]) 
				{
				FoundPath = TRUE;
				break;
				}
			*p++ = h;
			}
		if(FoundPath) break;			
		}
	if(FoundPath == FALSE) return(FALSE);
	
	for(h = 2; h < Vertices; h++)
		{
		Bdry[h] = PathNext[Bdry[h-1]];
		if(Bdry[h] == Bdry[0]) break;
		} 		
	return(h - 1);					
}

int Planar_Connected_(unsigned int length)                                       
{    
    /******************************************************************************************
        This routine is used to find the components produced when the cycle specified in
        Bdry[] is deleted from the graph. It is sufficient to know which component each vertex
        neighboring the deleted cycle belongs to. Given such a vertex, the routine uses
        breadth-first search to find the component in which the vertex lies.
    ******************************************************************************************/    
	
	int				CBIRV;
	     
    unsigned int   	h,
                    i,
                    j,
                    k,
                    NumComps,
                    *p,
                    *r;

	NumComps = 0;
	if(NumFaces == 0) NumComps = 1;
    for(h = 0;h < Vertices; h++) if(ZZ[h] == 0)
    	{
    	NumComps ++;
    	ZZ[h] = NumComps;
    	p = UpDate;
    	*p++ = h;
    	for(r = UpDate; r < p; r++)
    		{
    		i = *r;
    		for(k = 0; (j = AJ1[i][k]) < VERTICES; k++) if(ZZ[j] == 0)
    			{
    			*p++ = j;
    			ZZ[j] = NumComps;
    			}
    		}
    	}     
    if(NumComps > 1)
    	{
    	CBIRV = Check_Bridge_Interlacing(NumComps,length);
    	if(CBIRV == NON_PLANAR) return(NON_PLANAR);  
		if(CBIRV == FALSE) return(FALSE);
        }
    return(TRUE);
}

int Check_Bridge_Interlacing(unsigned int NumComps,unsigned int length)            
{   
    char            SideC[VERTICES];
    
    unsigned char   MaxC[VERTICES],
                	MidC[VERTICES],
                    MinC[VERTICES];
                            
    unsigned int    CompsFound,
    			   	h,
                    i,
                    j,
                    k,                    
                    MCh,
                    MCi,
                    mCh,
                    mCi,
                    *MyBdry,
                    MyUpDate[VERTICES],
                    *p,
                    *q,
                    *r,
                    *zz;
    
    MyBdry          = Bdry;
    zz              = ZZ;
    MyBdry[length]  = MyBdry[0];
                                        
    /******************************************************************************************
        For each bridge component formed when the cycle specified by the path in Bdry[] is
        deleted from the graph, find the first and last points at which the bridge meets the
        path.
    ******************************************************************************************/
	
    for(h = 1; h <= NumComps; h++) MinC[h] = 0;
    for(h = 1,i = 0; h <= length; h++)
    	{
		for(q = AJ1[MyBdry[h]]; (j = *q) < VERTICES; q++)
			{
			if((k = zz[j]) != VERTICES && MinC[k] == 0)
				{
				MinC[k] = h;
				if(++i == NumComps) break;
				}                
			}
		if(i >= NumComps) break;	
        }
    
    for(h = 1; h <= NumComps; h++) MaxC[h] = 0;
    for(h = length,i = 0; h > 0; h--)
    	{
		for(q = AJ1[MyBdry[h]]; (j = *q) < VERTICES; q++)
			{
			if((k = zz[j]) != VERTICES && MaxC[k] == 0)
				{
				MaxC[k] = h;
				if(++i == NumComps) break;
				}                   
			}
		if(i >= NumComps) break;	
        }
    
    for(h = 1; h <= NumComps; h++) MidC[h] = FALSE;
    for(h = 1; h <= NumComps; h++)
    	{
		for(i = MinC[h] + 1; i < MaxC[h]; i++)
			{
			for(q = AJ1[MyBdry[i]]; (j = *q) < VERTICES; q++) if(zz[j] == h)
				{
				MidC[h] = TRUE;
				break;
				}
			if(MidC[h] == TRUE) break;
			}
		}

	/**********************************************************************************************
		1)	Set SideC[i] = 2 if Component i contains a vertex in InPS. 
		2)	Set SideC[i] = -2 if: 
			a) 	There is a vertex of the path between MinC[i] and MaxC[i] which lies in the 
				current planar surface PS. 
			b) 	MaxC[i] = MinC[i] + 1, both MyBdry[MinC[i]] and MyBdry[MaxC[i]] are InPS and the 
				oriented edge GB(MyBdry[MaxC[i]],MyBdry[MinC[i]]) is an edge of the PS. 
			c) 	There is a component j, j != i, with MinC[i] <= MinC[j], MaxC[j] <= MaxC[i], 
				MidC[j] = TRUE, and SideC[j] = 2.	
	**********************************************************************************************/
			
	for(h = 1; h <= NumComps; h++) SideC[h] = 0;
	for(h = 1; h <= NumComps; h++) 
		{
		for(j = 0; j < Vertices; j++) if(zz[j] == h && InPS[j]) 
			{
			SideC[h] = 2;
			break;
			}
		}			
				
	for(h = 1; h <= NumComps; h++) if(SideC[h] != 2)
		{
		for(i = MinC[h] + 1; i < MaxC[h]; i++) if(InPS[MyBdry[i]] == 1)
			{
			SideC[h] = -2;
			break;
			}	
		if(MaxC[h] == MinC[h] + 1)
			{
			i = MyBdry[MinC[h]];
			j = MyBdry[MaxC[h]];			
			if(InPS[i] == 1 && InPS[j] == 1 && GB[j][i] == -1) SideC[h] = -2;
			}
			
		for(i = 1; i<= NumComps; i++)
			{
			if(i == h) continue;
			if(SideC[i] != 2) continue;
			if(MaxC[i] == MinC[i] + 1) continue;
			if(MinC[h] <= MinC[i] && MaxC[i] <= MaxC[h] && MidC[i] == TRUE)
				{
				SideC[h] = -2;
				break;
				}					
			}						
		}
     	
    /******************************************************************************************
            Determine whether components are forced to be embedded on the "inside" or on the
        "outside" of this cycle.
    ******************************************************************************************/
    
    for(i = 1; i <= NumComps; i++)
    for(j = 1; j <= NumComps; j++) AJ3[i][j] = FALSE;

	/****************************************************************************************** 
			Set AJ3[i][j] = TRUE if Bridge components i and j must be embedded on opposite 
		sides of this cycle. 	
	******************************************************************************************/
	
    for(h = 1; h <= NumComps; h++)
    for(i = h + 1; i <= NumComps; i++)
		{    
		mCh = MinC[h];
		MCh = MaxC[h];
		mCi = MinC[i];
		MCi = MaxC[i];
	
		if(mCh < mCi && mCi < MCh && MCh < MCi) 
			{
			AJ3[h][i] = AJ3[i][h] = TRUE;
			continue;
			}
		if(mCi < mCh && mCh < MCi && MCi < MCh)
			{
			AJ3[h][i] = AJ3[i][h] = TRUE;
			continue;
			}
		if(mCh == mCi && MCh == MCi)
			{
			if(MidC[h] && MidC[i]) 
				{
				AJ3[h][i] = AJ3[i][h] = TRUE;
				} 		
			continue;		
			}
		if(mCh <= mCi && MCi <= MCh && MidC[h])
			{
			for(j = MinC[i] + 1; j < MaxC[i]; j++)
				{
				for(q = AJ1[MyBdry[j]]; (k = *q) < VERTICES; q++) if(zz[k] == h)
					{
					AJ3[h][i] = AJ3[i][h] = TRUE;
					j = MaxC[i];
					break;
					}
				}
			continue;			
			}
		if(mCi <= mCh && MCh <= MCi && MidC[i])
			{
			for(j = MinC[h] + 1; j < MaxC[h]; j++)
				{
				for(q = AJ1[MyBdry[j]]; (k = *q) < VERTICES; q++) if(zz[k] == i)
					{
					AJ3[h][i] = AJ3[i][h] = TRUE;
					j = MaxC[h];
					break;
					}
				}
			continue;				
			}						
		}

	if(NumFaces == 0) SideC[1] = 2;
			
	for(h = 1,CompsFound = 0; h <= NumComps; h++) if(abs(SideC[h]) > 1)
		{
		r = p = MyUpDate;
		SideC[h] = SideC[h]/2;
		CompsFound ++;
		*p++ = h;
		while(r < p)
			{
			i = *r++;
			for(j = 1; j <= NumComps; j++) if(AJ3[i][j])
				{
				if((SideC[j] == SideC[i]) || (SideC[j] == 2*SideC[i])) return(NON_PLANAR);
				if(SideC[j] == 0)
					{
					SideC[j] = -SideC[i];
					*p++ = j;
					CompsFound ++;
					}				
				}
			}
		}

	for(h = 1; h <= NumComps; h++) if(SideC[h] == 0)
		{
		r = p = MyUpDate;
		SideC[h] = 1;
		CompsFound ++;
		*p++ = h;
		while(r < p)
			{
			i = *r++;
			for(j = 1; j <= NumComps; j++) if(AJ3[i][j])
				{
				if(SideC[j] == SideC[i]) return(NON_PLANAR);
				if(SideC[j] == 0)
					{
					SideC[j] = -SideC[i];
					*p++ = j;
					CompsFound ++;
					}
				}	
			}
		}	
	
    /******************************************************************************************
        Check whether it was possible to put all of the components on the "outside" of this
        cycle. If it was, return TRUE.
    ******************************************************************************************/

    for(h = 1,i = 0; h <= NumComps; h++) if(SideC[h] == 1) i++;
        if(i == NumComps) return(TRUE);
    
    /******************************************************************************************
        Temporarily delete the oriented edges leading from this cycle to components lying on
        the "outside". This insures that the next cycle will lie "inside" of this one.
    ******************************************************************************************/
        
    for(h = 1; h <= length; h++)
        {
        i = MyBdry[h];
        for(q = AJ1[i]; (k = *q) < VERTICES; q++)
            {
            if((j = zz[k]) == VERTICES) continue;            
            if(SideC[j] == 1 && GB[i][k] == 1)
                {
                *DeletedEdgePtr++    = i;
                *DeletedEdgePtr++    = k;
                GB[i][k]             = FALSE;    
                }
            }
        }
        
    /******************************************************************************************
        Temporarily delete the oriented edge of this cycle which leaves the first point at
        which an interior bridge is connected. Similarly, temporarily delete the oriented edge
        of this cycle which enters the last point at which an interior bridge is connected.
        Doing this insures that the next cycle will lie properly "inside" this one.
    ******************************************************************************************/

    for(h = 1,i = INFINITE,j = 0; h <= NumComps; h++) if(SideC[h] == -1)
        { 
        if(MinC[h] < i) i = MinC[h];
        if(MaxC[h] > j) j = MaxC[h];
        }
    
    if(GB[MyBdry[i]][MyBdry[i+1]] == 1)
    	{   
		*DeletedEdgePtr++             = MyBdry[i];
		*DeletedEdgePtr++             = MyBdry[i+1];
		GB[MyBdry[i]][MyBdry[i+1]]    = FALSE;    
    	}
    if(GB[MyBdry[j-1]][MyBdry[j]] == 1)
    	{	
		*DeletedEdgePtr++             = MyBdry[j-1];
		*DeletedEdgePtr++             = MyBdry[j];
		GB[MyBdry[j-1]][MyBdry[j]]    = FALSE;
    	}
    
    return(FALSE);        
}

int Find_Cut_Vertices(void)
{
    /*****************************************************************************************
        This routine uses depth-first-search to determine whether the graph specified by the
        adjacency-matrix AJ1[][] has a cut-vertex. The routine returns TRUE if the graph has
        a cut-vertex, and otherwise returns FALSE.
    *****************************************************************************************/
   
    unsigned int   	i,
                	j,
                    k,
                    *q;
                            
    unsigned int    VG[VERTICES],
                    root;
                         
    for(j = 0; j < Vertices; j++) Number[j] = 0;
    NumVert         = 1;
    root            = 0;
    Number[root]    = 1;
    Lowpt[root]     = 1;
    Father[root]    = 0;
    VG[root]        = 0;

    for(q = UpDate,*q = root; q >= UpDate; q--)
        {
        NEW_VERT:
        i = *q;
        for(k = VG[i]; (j = AJ1[i][k]) < VERTICES; k++)
            {
            if(Number[j] == 0)
                {
                NumVert     ++;
                Number[j]   = NumVert;
                Lowpt[j]    = NumVert;
                Father[j]   = i;
                VG[j]       = 0;
                VG[i]       = k + 1;
                q           ++;
                *q          = j;
                goto NEW_VERT;        
                }
            if(j != Father[i] && Number[j] < Lowpt[i]) Lowpt[i] = Number[j];        
            }
        if(Lowpt[i] < Lowpt[Father[i]]) Lowpt[Father[i]] = Lowpt[i];
        }
    
    /**********************************************************************************
        Check whether the root of the depth-first-search tree is a cut vertex. This 
        will be the case iff the root has more than one son.
    **********************************************************************************/
    
    for(i = k = 0; (j = AJ1[root][i]) < VERTICES; i++)
        if(Father[j] == root && ++k > 1) return(TRUE);
    
    /**********************************************************************************
        If k > 1, the root of the depth-first-search tree is a cut vertex.
        Otherwise, we look for other cut vertices.
    **********************************************************************************/
                        
    for(j = 0; j < Vertices; j++)
        {
        k = Father[j];
        if(Lowpt[j] >= Number[k] && k != root)
            return(TRUE);
        }    
    return(FALSE);
    
    /**********************************************************************************
        If j = Vertices, the Whitehead graph has no "cut vertex". So we return FALSE.
        Otherwise, the vertex Father[j] is a "cut vertex" and we return TRUE.
    **********************************************************************************/
}
 
int Print_Graph(int F1,int F2,int Pres,int HS)
{ 
	unsigned char 	c,
					h,
					i,
					j,
					k;
	
    int   			Error,
    				FoundPaths,
    				PrintedBdryInfo,
    				PrintedDualRelators,
                    PrintedRelators;
    	  			
    Error = Diagram_Data(1,F1,F2,Pres,HS);	
    if(Error == 1) 
    	{
    	printf("\n\nCan't display the diagram of Presentation %d. Sorry!\n",WhichInput + 1);
    	return(1);
    	}    
    if(!Connected)
    	{
    	printf("\n The diagram is not connected! Heegaard will only display data for connected diagrams! ");
    	printf("\n Rerun the offending presentation and Heegaard should divide it into connected summands.\n");
    	return(0);
    	}    
    if(NumGenerators == 1 || Vertices == 2)
    	{
    	printf("\n The diagram has only one generator and two vertices!");
    	printf("\n Heegaard will not display data for such diagrams!\n");
    	return(0);
    	}
    if(NumEdges > 3*(Vertices - 2))
    	{
    	printf("\n The reduced Whitehead graph has too many edges, i.e. E > 3V - 6.");
    	printf("\n Since the Diagram is obviously nonplanar, it will not be displayed.\n");
    	return(0);
    	}	 	
    if(MaxLength > VERTICES)
    	{
    	printf("\n The Diagram is nonplanar, and will not be displayed.\n");
    	return(0);
    	}	
    
    if(!NonPlanar)
		{	
		printf("\n\nII) Vertices in the boundary of each face of the Heegaard diagram ");
		printf("in clockwise order are:\n\n");
		for(i = 1; i <= NumFaces; i++)
			{
			printf("F%d) ",i);
			for(j = 0; (h = Face[i][j]) < VERTICES; j++)
				{
				if(h & 1)
					c = h/2 + 97;
				else
					c = h/2 + 65;
				printf("%c",c);	
				}
			if(i < NumFaces) printf(", ");	
			}

		printf("\n\nNote: Heegaard chose the cycle '");
		for(i = 0; i < MaxLength; i++)
			{
			j = SaveBdry[i];
			if(j & 1)
				c = j/2 + 97;
			else
				c = j/2 + 65;
			printf("%c",c);  	
			}
		printf("' to be the boundary of the 'infinite' face.");	
		
		printf("\n\nIII) CO[v] lists the vertices in the link of vertex v in counter-clockwise cyclic order ");
		printf("starting with the 'first-vertex' in lexicographic order connected to v.\n\n");
	
		for(i = 0; i < Vertices; i++) if(VWG[i])
			{
			if(i & 1)
				c = i/2 + 97;
			else
				c = i/2 + 65;
			printf("CO[%c] = ",c);
			for(j = 0; j < Vertices; j++) if(A[i][j] && i != j) break;
			if(j & 1)
				c = j/2 + 97;
			else
				c = j/2 + 65;
			printf("%c",c);
			k = CO[i][j];
			while(k != j) 
				{
				if(k & 1)
					c = k /2 + 97;
				else
					c = k/2 + 65; 
				printf("%c",c);
				k = CO[i][k];
				}
			if(i < Vertices - 1) printf(", ");	
			}
		}
    
    if(Connected)
    	{
    	for(i = 0; i < MaxLength - 1; i++)
    		{
    		j = SaveBdry[i];
    		k = SaveBdry[i+1];
    		if(!A[j][k]) return(Error);
    		}
    	j = SaveBdry[0];
    	if(!A[j][k]) return(Error);   		
    	Gauss_Seidel();
    	Diagram_Data_for_Graphviz(F2,Pres,HS);
    	}

	
	PrintedBdryInfo = 		FALSE;
	PrintedDualRelators = 	FALSE;
	FoundPaths = 			FALSE;
	PrintedRelators = 		FALSE;
GET_RESPONSE1: 
	printf("\n");
GET_RESPONSE2:	
	if((Error == 0 || Error == 3) && Connected && NumGenerators > 1 && Batch == FALSE)
		{
		if(Error == 3) PrintedBdryInfo = PrintedDualRelators = FoundPaths = TRUE;
		if(PrintedBdryInfo == FALSE && FoundPaths == FALSE)
		printf("\nHIT 'b' FOR INFO SHOWING WHICH FACES OF THIS DIAGRAM FORM BDRY COMPONENTS.");
		if(PrintedDualRelators == FALSE)
		printf("\n   HIT 'd' TO SEE THE 'DUAL' RELATORS FOR THIS DIAGRAM.    ");
		if(F1)
			{
			printf("\n      HIT 'n' TO SEE THE NEXT DIAGRAM.    ");
			if(FoundPaths == FALSE)
				{
				printf("\n         HIT 'p' TO SEE PATHS CONNECTING FACES OF THIS DIAGRAM.");
				printf("\n            HIT 'q' TO QUIT VIEWING DIAGRAMS.    ");
				if(PrintedRelators == FALSE)
					{
					if(F2)
						printf("\n               HIT 'v' TO REVIEW PRES %d OF HS %d.    ",Pres,HS);
					else
						printf("\n               HIT 'v' TO REVIEW PRESENTATION %d.    ",WhichInput + 1);
					}	
				}
			else
				{
				printf("\n         HIT 'q' TO QUIT VIEWING DIAGRAMS.    ");	
					if(PrintedRelators == FALSE)
					{
					if(F2)
						printf("\n               HIT 'v' TO REVIEW PRES %d OF HS %d.    ",Pres,HS);
					else
						printf("\n               HIT 'v' TO REVIEW PRESENTATION %d.    ",WhichInput + 1);
					}				
				}	
			}
		else
			{
			if(FoundPaths == FALSE)
				printf("\n         HIT 'p' TO SEE PATHS CONNECTING FACES OF THIS DIAGRAM.");
			printf("\n            HIT 'q' TO QUIT VIEWING INFO FOR THIS DIAGRAM.    ");
			if(PrintedRelators == FALSE)
				{
				if(F2)
					printf("\n               HIT 'v' TO REVIEW PRES %d OF HS %d.    ",Pres,HS);
				else
					printf("\n               HIT 'v' TO REVIEW PRESENTATION %d.    ",WhichInput + 1);
				}				
			}	
_OPTIONS:
		if(Batch == FALSE)
			{
			switch(WaitkbHit())
				{
				case 'b':
					if(PrintedBdryInfo) goto GET_RESPONSE1;
					Print_Bdry_Comp_Info(F2,Pres,HS);
					PrintedBdryInfo = TRUE;
					goto GET_RESPONSE1;
				case 'd':
					if(PrintedDualRelators) goto GET_RESPONSE1;                               
					Print_DualRelators(F1,F2,Pres,HS);
					PrintedDualRelators = TRUE;
					goto GET_RESPONSE1;
				case 'n':
					if(F1) return(1);
					else goto _OPTIONS;	
				case 'p':
					if(FoundPaths) goto GET_RESPONSE1;
					Find_Cancellation_Paths(PrintedBdryInfo,F2,Pres);	
					FoundPaths = TRUE;
					goto GET_RESPONSE1;
				case 'q':
					if(F2) return(2);
					if(F1)
						{
						WhichInput = NumFilled + 1;
						return(0); 
						}
					else return(1);	
				case 'v':
					if(PrintedRelators) goto GET_RESPONSE1;
					PrintedRelators = TRUE;
					if(NumRelators == 1)
						{
						if(F2)
							printf("\n\nThe Relator of Pres %d of HS %d is: \n",Pres,HS);
						else
							printf("\n\nThe Relator of Presentation %d is: \n",WhichInput + 1);					
						}
					else
						{
						if(F2)
							printf("\n\nThe Relators of Pres %d of HS %d are: \n",Pres,HS);
						else
							printf("\n\nThe Relators of Presentation %d are: \n",WhichInput + 1);										
						}	
					Print_Relators(Relators, NumRelators);
					goto GET_RESPONSE2;	       
				default:
					if(Batch == FALSE) SysBeep(5);
					goto _OPTIONS;    
				}
			} 
		} 
	if(Batch == 5 && Error == 0)
		{
		if(B5PrintBdryComps) Print_Bdry_Comp_Info(F2,Pres,HS);			
		if(B5PrintDualRelators) Print_DualRelators(F1,F2,Pres,HS);			
		if(B5PrintPaths) Find_Cancellation_Paths(B5PrintBdryComps,F2,Pres);		
		}			                                                 
    return(1);
}

int Diagram_Data(int PrintOut,int F1,int F2,int Pres,int HS)
{                     
    unsigned char   *p,
                    x,
                    y;
                                       
    int    			Error = FALSE,
    				i,
    				j,
        			k,
            		n,
            		SWhichInput;                

    unsigned int 	Diagram_Main();
    
if(PrintOut == 1)    
    
    for(k = 0; k < PrintOut; k++)
        {       
        if(Batch == FALSE)
        	{
			if(F2)
				{
				printf("\n\n*********************************************************************************");
				printf("\n\n               Data For The Diagram of Pres %d of HS %d",Pres,HS);
				}
			else
				{
				printf("\n\n*********************************************************************************");
				printf("\n\n               Data For Diagram %d of the Initial Presentation %s",WhichInput + 1,PresName);
				}
			printf("\n\nGenerators %d, Relators %d, Length %lu.",NumGenerators,NumRelators,Length);	
        	}
        
        printf("\n\nI) The following table gives the number of edges joining each pair of vertices.\n\n");
        
        for(i = 0; i < Vertices - 1; i++)
            {
            for(j = i + 1; j < Vertices && !A[i][j]; j++) ;
            if(j >= Vertices) continue;
            if(i & 1)
                x = i/2 + 97;
            else
                x = i/2 + 65;
            if(i) printf(", (%c --> ",x);
            else  printf("(%c --> ",x);
            		 
            for(j = i + 1, n = 0; j < Vertices; j++)
                {
                if(A[i][j])
                    {
                    if(j & 1)
                        y = j/2 + 97;
                    else
                        y = j/2 + 65;
                    n++;
                    if(n == 1)   
                    	printf("%c%u",y,A[i][j]);
                    else
                    	printf(",%c%u",y,A[i][j]);	  
                    }    
                }
            printf(")");        
            }       

        if(!Connected)
            {
            Error = 1;
            printf("\n\nThe diagram is not connected. So complete data is unavailable.");
            goto END;
            }        
        if(NonPlanar)
            {
            Error = 2;
            printf("\n\nThe diagram is nonplanar. So complete data is unavailable.");
            goto END;
            }  
   
        if(SepPairs)
            {
            Error = 3;
            if(UDV[WhichInput] == ANNULUS_EXISTS)
                {
                p = *SUR[WhichInput][0];
                x = *p++;
                y = *p++;                
                printf("\n\nThe pair of vertices (%c,%c) separate the diagram.",x,y);
                printf("\nThe component consisting of vertice(s) {%c",*p);
                p++;
                while((x = *p) != '@')
                    {
                    printf(",%c",x);
                    p++;
                    }
                printf("}");    
                p++;        
                printf("\nlies in an annulus which swallows the component and otherwise follows the curve:");
                printf("\n%s.",p);
                }
            else
                {
                if(UDV[WhichInput] == V2_ANNULUS_EXISTS)
                    {
                    p = *SUR[WhichInput][0];
                    printf("\n\nThere exists an annulus which swallows vertice(s) {%c",*p);
                    p++;
                    while((x = *p) != '@')
                        {
                        printf(",%c",x);
                        p++;
                        }
                    printf("}");    
                    p++;        
                    printf("\nand otherwise follows the curve:");
                    printf("\n%s.",p);
                    }        
                else
                if(UDV[WhichInput] == SEP_PAIRS)
                        printf("\n\nVertices '%c' and '%c' separate the Whitehead graph. So complete data is unavailable.",
                        x = LSP[WhichInput],y = LSQ[WhichInput]);    
                }    
            }
        if(NumGenerators > 1 && Connected && !SepPairs && !NonPlanar)    
            {
            if(k == 0)
                {
                TestRealizability1 = TRUE;
                switch(Diagram_Main())
                    {
                    case TOO_LONG:
                        printf("\n\nThe presentation is too long. So complete data is unavailable.");
                        TestRealizability1 = FALSE;
                        Error = TRUE;
                        goto END;
                    case FATAL_ERROR:
                        printf("\n\nThe presentation is not realizable. So complete data is unavailable.");
                        TestRealizability1 = FALSE;
                        Error = TRUE;
                        goto END;
                    case NON_UNIQUE_1:
                        if(UDV[WhichInput] < DONE) UDV[WhichInput] = NON_UNIQUE_1;
                        break;
                    case NON_UNIQUE_2:
                        if(UDV[WhichInput] < DONE) UDV[WhichInput] = NON_UNIQUE_2;
                        break;
                    case NON_UNIQUE_3:
                        if(UDV[WhichInput] < DONE) UDV[WhichInput] = NON_UNIQUE_3;
                        break;
                    case NON_UNIQUE_4:
                        if(UDV[WhichInput] < DONE) UDV[WhichInput] = NON_UNIQUE_4;
                        break;
                    case V2_ANNULUS_EXISTS:
                    	if(F2 && UDV[WhichInput] < DONE) UDV[WhichInput] = V2_ANNULUS_EXISTS;
                        Error = TRUE;
                        break;    
                    }
                TestRealizability1 = FALSE;
                }        
        
            printf("\n\nFor each (X,x) pair of vertices with (X,x) = (A,a), (B,b) ... ,(Z,z):");
            printf("\n1) Number the edges at vertex X counter-clockwise about vertex X giving the ");
            printf("'first-edge' at vertex X number 0.");
            printf("\n2) Note the 'first-edge' at vertex V is the first edge in counter-clockwise order");
            printf(" about V which connects V to V's 'first-vertex'. (See III below for V's 'first-vertex'.)");
            printf("\n3) For x = a,b ... ,z, number the edges at vertex x clockwise about x, giving the ");
            printf("'first-edge' at x the number shown in the following list:\n\n");
            
    
            printf("(%u",OSA[0] % VA[0]);    
            for(i = 2; i < Vertices; i += 2) printf(",%u",OSA[i] % VA[i/2]);
            printf(")");

            SWhichInput = WhichInput;
                    
            switch(UDV[SWhichInput])
                {
                 case NON_UNIQUE_4:
                    printf("\n\n     Note,the diagram is not unique because there is a generator which appears");
                    printf("\nwith only one exponent and that exponent is greater than 6.");
                    break;
                case NON_UNIQUE_3:
                    printf("\n\n     Note,the diagram is not unique because there is a generator which appears");
                    printf("\nonly with exponent 5.");
                    break;
                case NON_UNIQUE_2:
                    printf("\n\n     Note,the diagram is not unique because there is a generator which appears");
                    printf("\nonly with exponent 3 or only with exponent 4 and this exponent occurs more than once.");
                    break;
                case NON_UNIQUE_1:
                    printf("\n\n     Note,the diagram is not unique because there is a generator which appears");
                    printf("\nwith only one exponent, either 3,4 or 6, and a needed symmetry does not exist.");
                    break;
                case ANNULUS_EXISTS:
                    p = *SUR[SWhichInput][0];
                    x = *p++;
                    y = *p++;                
                    printf("\n\nThe pair of vertices (%c,%c) separate the diagram.",x,y);
                    printf("\nThe component consisting of vertice(s) { %c",*p);
                    p++;
                    while((x = *p) != '@')
                        {
                        printf(",%c",x);
                        p++;
                        }
                    printf(" }");    
                    p++;        
                    printf("\nlies in an annulus which swallows the component and otherwise follows the curve:");
                    printf("\n%s.",p);
                    Error = TRUE;
                    break;
                case V2_ANNULUS_EXISTS:
                    p = *SUR[SWhichInput][0];
                    printf("\n\nThere exists an annulus which swallows vertice(s) { %c",*p);
                    p++;
                    while((x = *p) != '@')
                        {
                        printf(",%c",x);
                        p++;
                        }
                    printf(" }");    
                    p++;        
                    printf("\nand otherwise follows the curve:");
                    printf("\n%s.",p);
                    Error = TRUE;
                    break;                
                }            
            }
        }

END:
    return(Error);            
} 

void Diagram_Data_for_Graphviz(int F2,int Pres,int HS)
{
	unsigned char	x,
				    y;
				    
	int				i,
					j,
					NumPts;
					
	long			DeltaX,
					DeltaY,
					DeltaSquared,
					MinDist,
					MinDistSquared;
	
	if(Batch == FALSE)
		{
		if((Gvizdata = fopen("Heegaard_Diagrams.dot","w+")) == NULL)
			{
			printf("\n\nUnable to create file Gvizdata used by Graphviz() to display Heegaard's Heegaard diagrams");
			return;
			}						
	
		fprintf(Gvizdata,"graph G{layout = neato; model = circuit; size = \04210.0,8.0\042; ratio = fill ;\n");
		if(F2)
			fprintf(Gvizdata,"label = \042Diagram of Pres %d of HS %d of the Initial Presentation %s\042; \n",Pres,HS,PresName);	
		else
			fprintf(Gvizdata,"label = \042Diagram of Presentation %d of the Initial Presentation %s\042; \n",
			WhichInput + 1, PresName);
		}
	else
		{
		printf("\n\n****************************************************************************************");
		printf("\nThe following lines describe the Heegaard diagram in Graphviz() readable form.");
		printf("\nCopy and paste into 'Heegaard_Diagrams.dot to have Graphviz() display the diagram.");
		
		printf("\n\n graph G{layout = neato; model = circuit; size = \04210.0,8.0\042; ratio = fill ;\n");
		if(F2)
			printf(" label = \042Diagram of Pres %d of HS %d of the Initial Presentation %s\042; \n",Pres,HS,PresName);	
		else
			printf(" label = \042Diagram of Presentation %d of the Initial Presentation %s\042; \n",WhichInput + 1, PresName);		
		}	
	
	MinDist = 15;
	MinDistSquared = MinDist*MinDist;
	
	for(i = NumPts = 0; i < Vertices - 1; i++) if(Flags[i])
		{
		for(j = i + 1; j < Vertices; j++) if(Flags[j])
			{
			DeltaX = labs(X[i]-X[j]);
			DeltaY = labs(Y[i]-Y[j]);
			if(DeltaX > MinDist || DeltaY > MinDist || DeltaX + DeltaY > MinDist) continue;
			DeltaSquared = DeltaX*DeltaX + DeltaY*DeltaY;
			if(DeltaSquared > MinDistSquared) continue;
			if(!A[i][j] && 4*DeltaSquared > MinDistSquared) continue;	
			if(Flags[i] > 1) 
				{
				Flags[i] ++;
				NumPts ++;
				}
			if(Flags[j] > 1)
				{
				Flags[j] ++;
				NumPts ++;
				}
			}
		}
		
	if(NumPts)
		{
		for(i = 0; i < Vertices - 1; i++) if(Flags[i] == 3)
			{
			for(j = i + 1; j < Vertices; j++) if(Flags[j] > 2)
				{
				DeltaX = labs(X[i]-X[j]);
				DeltaY = labs(Y[i]-Y[j]);
				if(DeltaX > MinDist || DeltaY > MinDist || DeltaX + DeltaY > MinDist) continue;
				DeltaSquared = DeltaX*DeltaX + DeltaY*DeltaY;
				if(DeltaSquared > MinDistSquared) continue;
				if(!A[i][j] && 4*DeltaSquared > MinDistSquared) continue;
				if(4*DeltaSquared > MinDistSquared)
					{
					Flags[i] = 2;
					NumPts --;
					}			
				}
			}
		}		
	
	if(Batch == FALSE)
		{	
		if(NumPts)
			{
			fprintf(Gvizdata,"node [shape = point, height = 0.05]; { \n");
			for(i = 0; i < Vertices; i++) if(Flags[i] > 2)
				{
				if(i & 1) x = i/2 + 97;
				else      x = i/2 + 65;
				fprintf(Gvizdata,"%c [pos = \042%d,%d!\042]; ",x,X[i],Y[i]);	
				}
			fprintf(Gvizdata,"} \n");
			}	
		
		fprintf(Gvizdata,"node [shape = square, fontsize = 8, height = 0.1, style = white] \n");

		for(i = 0; i < Vertices; i++) if(Flags[i] == 1 || Flags[i] == 2)
			{
			if(i & 1) x = i/2 + 97;
			else      x = i/2 + 65;
			fprintf(Gvizdata,"%c [pos = \042%d,%d!\042]; ",x,X[i],Y[i]);	
			}
	
		fprintf(Gvizdata,"\n edge [fontsize = 8]; { ");
	
		for(i = 0; i < Vertices - 1; i++)
			{
			if(i & 1) x = i/2 + 97;
			else      x = i/2 + 65;
			for(j = i+1; j < Vertices; j++) if(A[i][j])
				{
				if(j & 1) y = j/2 + 97;
				else      y = j/2 + 65;
				fprintf(Gvizdata,"%c -- %c ; ",x,y);
				}
			}
		
		fprintf(Gvizdata,"}}\n\n");
		fclose(Gvizdata);
    	}
    if(Batch)
    	{
		if(NumPts)
			{
			printf("node [shape = point, height = 0.05]; { \n");
			for(i = 0; i < Vertices; i++) if(Flags[i] > 2)
				{
				if(i & 1) x = i/2 + 97;
				else      x = i/2 + 65;
				printf("%c [pos = \042%d,%d!\042]; ",x,X[i],Y[i]);	
				}
			printf("} \n");
			}	
		
		printf("node [shape = square, fontsize = 8, height = 0.1, style = white] \n");

		for(i = 0; i < Vertices; i++) if(Flags[i] == 1 || Flags[i] == 2)
			{
			if(i & 1) x = i/2 + 97;
			else      x = i/2 + 65;
			printf("%c [pos = \042%d,%d!\042]; ",x,X[i],Y[i]);	
			}
	
		printf("\n edge [fontsize = 8]; { ");
	
		for(i = 0; i < Vertices - 1; i++)
			{
			if(i & 1) x = i/2 + 97;
			else      x = i/2 + 65;
			for(j = i+1; j < Vertices; j++) if(A[i][j])
				{
				if(j & 1) y = j/2 + 97;
				else      y = j/2 + 65;
				printf("%c -- %c ; ",x,y);
				}
			}
		
		printf("}}\n\n");  	
    	}	 
}

void Gauss_Seidel(void)
{    
    /****************************************************************************************** 
        This routine determines where the vertices of the Heegaard diagram are to be located
        in the plane. First the locations of the vertices that belong to the boundary of the
        "infinite" face of the diagram are determined. Then each remaining vertex of the
        diagram is located at the barycenter of the locations of its neighbors. Determining 
        the locations of these vertices requires solving a set of linear equations. We do this
        using the Gauss-Seidel method.
    ******************************************************************************************/
                                        
    int 	converge,
    		h,
    		i,
    		j,
    		k,
            NumVert,
            PVert,
            Vert;
    
    long    bottom,
            left,
            RIC[VERTICES],
            right,
            top,
            x,
            X1,
            X2,
            XF[VERTICES],
            y,
            Y1,
            Y2,
            YF[VERTICES],
            z;
                                
    for(i = 0; i < Vertices; i++)
        {
        /* Put every vertex at screen center initially. */
        
        XF[i] = 290000;    
        YF[i] = 225000;	
        if(VWG[i]) Flags[i] = 2;
        else Flags[i] = 0;
        }    
        
    /******************************************************************************************
        Plot the vertices of the "infinite" face of the graph. These vertices will be spaced 
        around the perimeter of a rectangle on the screen -- unless there are only 3 vertices
        in the boundary of the "infinite" face. So that the cyclic orders of the vertices are
        represented correctly, the order in which vertices appear in the boundary of the
        infinite face is such that the interior of the infinite face lies to the right-hand
        side of its oriented boundary.
    ******************************************************************************************/
    
    if((MaxLength < 2) || (MaxLength > VERTICES)) goto _DONE;   
    
    if(MaxLength == 3)
        {
        x = 30000;
        y = 30000;
		for(i = 0; i < MaxLength ; i++)	
            {
            j = SaveBdry[i];
            XF[j] = x;
            YF[j] = y;    
         	switch(x)
				{
				case 30000:
					x = 550000;
					y = 30000;
					break;
				case 550000:
					x = 290000;
					y = 420000;
					break;
				}
            /* Set Flags[j] = 1 so that vertex j will not be moved. */    
            Flags[j] = 1;
            }    
        }
    else    
        {
 		top = 31000;
        left = 31000;
        right = 549000;				
 		bottom = 419000;
        i = MaxLength/4;
        switch(MaxLength % 4)
            {
            case 0:
                X2 = X1 = 520000/i;
                Y2 = Y1 = 390000/i;
                break;
            case 1:
                X1 = 520000/(i+1);
                X2 = 520000/i;
                Y2 = Y1 = 390000/i;	           
                break;
            case 2:
                X2 = X1 = 520000/(i+1);
                if(i)
                Y2 = Y1 = 390000/i;               
                break;
            case 3:
                X2 = X1 = 520000/(i+1);
                Y1 = 390000/(i+1);
                if(i)
                Y2 = 390000/i;
                break;
            }
        x = 30000;
        y = 30000;        
 		for(i = MaxLength - 1; i >= 0; i--)	
            {
            if(y < top && x > left) x -= X1;
            else
            if(x < left && y < bottom) y += Y1;
            else
            if(y > bottom && x < right) x += X2;
            else
            if(x > right && y > top) y -= Y2;
            j = SaveBdry[i];
            XF[j] = x;
            YF[j] = y;
            /* Set Flags[j] = 1 so that vertex j will not be moved. */
            Flags[j] = 1;
            }    
        }            
        
    for(i = 0; i < Vertices; i++)
        {
        /* Move the graph center from (290000,225000) to the origin (0,0). */
        
        XF[i] -= 290000;
        YF[i] -= 225000;
        }
                    
    /******************************************************************************************
        Save the valences of those vertices with nonzero valence in the array RIC[].
    ******************************************************************************************/
    
    if(NonPlanar || !Connected)
        {
        for(i = 0;i < Vertices; i++) if(VWG[i])
        RIC[i] = VWG[i];
        }
    else for(i = 0;i < Vertices; i++) if(Flags[i] == 2)
        {
        
        /**************************************************************************************
            Add some "virtual" edges to the graph so that the graph will have a more visually
            appealing embedding on screen.
        **************************************************************************************/
            
        NumVert = 0;
        for(h = 0; (j = AJ1[i][h]) < VERTICES; h++)
            {
            Vert = j;
            for(k = 0; (k < NumVert) && AJ3[i][k] != Vert; k++) ;
            if(k == NumVert)
                {
                AJ3[i][NumVert] = Vert;
                NumVert ++;
                }
            Vert = CO[j][i];
            for(k = 0; (k < NumVert) && AJ3[i][k] != Vert; k++) ;
            if(k == NumVert)
                {
                AJ3[i][NumVert] = Vert;
                NumVert ++;
                }
            Vert = i;
            do
                {
                PVert = Vert;
                Vert = CO[j][PVert];
                }
            while(Vert != i);
            Vert = PVert;    
            for(k = 0; (k < NumVert) && AJ3[i][k] != Vert; k++) ;
            if(k == NumVert)
                {
                AJ3[i][NumVert] = Vert;
                NumVert ++;
                }
            }
        AJ3[i][NumVert] = VERTICES;
        z = NumVert + 2*VWG[i];
        RIC[i] = z;	
        }

    /**********************************************************************************************
        Iterate until two successive iterations don't move any interior vertex by more than ERROR.
    ***********************************************************************************************/
    
    if(NonPlanar || !Connected)
        {
        converge = TRUE;
        k = 0;
        while (1)
            {
            k ++;
            for(i = 0; i < Vertices; i++) if(Flags[i] == 2)
                {
                x = y = 0;
                z = RIC[i];
                for(h = 0; (j = AJ1[i][h]) < VERTICES; h++)    
                    {
                    x += XF[j];
                    y += YF[j];
                    }
                x = x/z;
                y = y/z;                                
                if(converge)
                    if((labs(x - XF[i]) + labs(y - YF[i])) > 100) converge = FALSE;                        
                XF[i] = x;
                YF[i] = y;
                }
            if (++converge == 2 || k > 3000) break;                        
             }
         }    
    else
        {                    
        converge = TRUE;
        k = 0;
        while (1)
            {
            k ++;
            for(i = 0; i < Vertices; i++) if(Flags[i] == 2)
                {
                x = y = 0;
                z = RIC[i];
                for(h = 0; (j = AJ3[i][h]) < VERTICES; h++)    
                    {
                    if(A[i][j])
                        {
                        x += 3*XF[j];
                        y += 3*YF[j];
                        }
                    else
                        {
                        x += XF[j];
                        y += YF[j];
                        }
                    }
                x = x/z;
                y = y/z;                                
                if(converge)
                    if((labs(x - XF[i]) + labs(y - YF[i])) > 100) converge = FALSE;                        
                XF[i] = x;
                YF[i] = y;
                }
            if (++converge == 2 || k > 3000) break;                        
             }   
         }    
     
    /******************************************************************************************
        Shrink the interior of the complement of the 'infinite' face of the graph slightly so
        that vertices which should not appear on the boundary of the infinite face do not
        appear there. Then translate the center of the graph to the center of the screen.
    ******************************************************************************************/
    
     for(i = 0; i < Vertices; i++)
        {
        if(Flags[i] == 2)
            {
            XF[i] *= 95;
            XF[i] = XF[i]/100;
            YF[i] *= 95;
            YF[i] = YF[i]/100;
            }
            
        /* Move the graph center from the origin (0,0) to (290000,225000). */ 
           
        XF[i] += 290000;
        YF[i] += 225000;
        }
        
_DONE:        
     /*****************************************************************************************
             Convert the long integer values in XF[] and YF[] to integers in X[] and Y[].
     *****************************************************************************************/    
     
     for(i = 0; i < Vertices; i ++) 
        {
        X[i] = XF[i]/1000;
        Y[i] = YF[i]/1000;
        }                    
}
    
void Print_Bdry_Comp_Info(int F2,int Pres,int HS)
{
    unsigned char  	x,
    				*p;
    				
    int            	i,
                    j,
                    k,
                    n,
                    ParallelRel;
    
    if(F2)
    	printf("\n\n                    DATA ABOUT THE BOUNDARY COMPONENTS OF THE DIAGRAM OF PRES %d OF HS %d:",Pres,HS);    
    else
    	printf("\n\n                    DATA ABOUT THE BOUNDARY COMPONENTS OF DIAGRAM %d:",WhichInput + 1);

	Get_Bdry_Comps(TRUE,FALSE,WhichInput);
	
    ParallelRel = 0;    
    for(i = 0; i <= NumGenerators && BCWG[i] < BDRY_UNKNOWN; i++) if(BCWG[i])
        {
        for(j = 1; j <= NumBdryComps; j++) if(GBC[j] == i)
            {
            if(GBC[j] == 0)
                {
                for(k = 1,n = 0; k <= NumFaces; k++) if(BCF[k] == j) n++;
                if(n == 0)
                    {
                    ParallelRel ++;
                    continue;
                    }
                }
            printf("\n\nFaces which 'form' boundary component %d of genus %d.\n\n",j,i);
            for(k = 1,n = TRUE; k <= NumFaces; k++) if(BCF[k] == j)
                {
                if(n)
                	{
                	printf(" F%d) ",k);
                	n = FALSE;
                	}
                else
                	printf(", F%d) ",k);
                p = Face[k];
                while((x = *p++) < VERTICES)
                    {
                    if(x & 1)
                        x = x/2 + 97;
                    else
                        x = x/2 + 65;    
                    printf("%c",x);
                    }
                }
            }
        if(i == 0) switch(ParallelRel)
            {
            case 0:
                break;
            case 1:
                printf("\n\nThe diagram also has a pair of 'parallel' relators which form a boundary component of genus 0.");            
                break;
            default:    
                printf("\n\nThe diagram also has %d pairs of 'parallel' relators which form %d boundary components of genus 0.",
                    ParallelRel,ParallelRel);
                break;    
            }
        }
}    

