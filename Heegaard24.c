#include "Heegaard.h"
#include "Heegaard_Dec.h"

char			SFoundShorterRelator;

unsigned char	**BestNewRelator = NULL,
				CurrentBdryComp,
				*MarkedPathsL = NULL,
				*NewRelator = NULL,
				**PM = NULL,
				*PM_To = NULL,
				**PP = NULL,
				*PP_From = NULL,
				*PP_To = NULL,
				RelatorReplaced,
				*SMinCircuitPaths = NULL,
				*SaveTL = NULL,
				*SaveTR = NULL,
				SCurrentBdryComp,
				*T1 = NULL,
				**Temp;
				
int				Big_Number = 50000,
				**P_From_Face = NULL;
				
unsigned int	MaxLengthReduction,
				NumPaths,
				*PLength = NULL;
				
unsigned long	SSSSLength;

/******************************* Functions in Heegaard24.c ********************************	
L 1033 Find_Flow_D(char Flag)
L   37 PM_Check_When_Bdry_Exists(char Flag)
******************************************************************************************/												
					
int PM_Check_When_Bdry_Exists(char Flag)
{
	/********************************************************************************************
			Heegaard uses the routines in this file to search for pseudo-minimal presentations
		when a manifold M has non-empty boundary, and all of M's boundary components are tori.
		In principle, the methods this routine uses for toral boundary components can be 
		extended to larger genus boundary components, but they are not currently implemented.
		This means that if S is a boundary component of M with genus > 1, currently Heegaard 
		only locates bandsums of relators in S which result in a reduction of length. (If
		no such bandsums exist, Heegaard labels M as "quasi-pseudo-minimal".)
		
			Given a set of simple closed curve realtors R in a Heegaard surface F, the problem 
		is to locate a simple closed curve r in F, disjoint from the curves in R, such that an 
		appropriate curve in R can be replaced by r, creating a new set of relators R' in F 
		such that |R'| < |R|, while keeping the normal closure of the curves in R in F equal 
		to the normal closure of the curves in R' in F. (As usual, lengths such as |R| are 
		measured with respect to a complete set of meridian disks Delta of the underlying 
		handlebody H chosen so Delta intersects the curves in R minimally.)
			
			Locating r when M has non-empty boundary is more complicated than when M is closed, 
		and because of this additional complexity, is currently limited to manifolds whose 
		boundary components are all tori. This means that if S is a boundary component of 
		genus > 1, currently Heegaard only locates bandsums of relators in S which result in a 
		reduction of length.
			
		
			So suppose T is a punctured torus obtained from F by cutting F open along the 
		curves in R. 
			Then Heegaard's approach is as follows: 
			1) Heegaard first locates a minimal length nonseparating simple closed curve 
		alpha in T. 
			2) Next Heegaard locates a minimal length path beta in T with endpoints on alpha
		such that beta leaves one side of alpha and returns to the other side of alpha.
		Then the minimality of |alpha| and |beta| guarantees that if a simple closed curve r 
		exists with the properties mention above, then there exists r' disjoint from alpha
		union beta with |r'| <= |r| which also satisfies the requirements.
			3) Suppose C is the boundary of a regular neighborhood of alpha and beta in T.
		Then C is a separating simple closed curve in T which cuts T into a punctured torus T' 
		containing alpha and beta and a punctured disk D whose boundary components are C and
		copies of some curves in R.
		
	********************************************************************************************/							
	
	char			Chi;
							
	unsigned char 	*BadToralBdry = NULL,
					*BdryCompFace = NULL,
					CompNum,
					*FacesVisited = NULL,
					*FacesVisitedList = NULL,
					FoundNew,
					InitialFace,
					*InTree = NULL,
					LSidePath,
					mm,
					MyFace,
					NewFace,
					NonSepCircuit,
					NumBadNonToralBdryComps,
					NumBadToralBdryComps,
					NumCompBdries,
					NumCompFaces,
					NumCompPaths,
					NumGenusZeroBdryComps,
					NumLPaths,
					NumPathsInCircuit,
					*p,
					PossibleNewTerminalFace,
					*q,
					*r,
					RRV,
					STLj,
					STRj,
					TerminalFace,
					*T2 = NULL,
					tl,
					tr,
					*TreePreviousVertex = NULL,
					TreeSize,
					*TreeVertex = NULL,
					*TreeMarkedVertex = NULL,
					V1,
					V2,
					V3,
					V4,
					x,
					y;
													
	int 			ChosenPath,
					Error,
					ii,
					k,
					*PathsInCircuit = NULL,
					*pp,
					ss,
					*TreePreviousPath = NULL;
							
	unsigned int 	c,
					CumulativeLength,
					d,
					e,
					edge,
					EL[6*VERTICES],
					ee,
					h,
					i,
					j,
					length,
					max,
					MinCircuitLength,
					NumCircuitsFound,
					*ppp,
					*rrr,
					*TreePathLength = NULL,
					TreeTrialMinPathLength,
					v,
					vertex,
					vertexRS,
					vertexLE,
					w;
	
	long 			HSS;
	
	if(NumRelators < 2) return(2);
	
	Error = 0;
	NumPaths = 0;
	SSSSLength = Length;
	NumDiagrams ++;	
	Vertices = 2*NumGenerators;	
	RRV = 0;
	if(Flag)
		{	
		if(Find_Flow_A(NORMAL,0)) return(TOO_LONG);	
		Get_Matrix();
		for(i = 0; i < Vertices; i++) ZZ[i] = 0;
		if(Connected_(0,0) == FALSE) return(TOO_LONG);
		if(Sep_Pairs(0,0,1)) 
			{
			if(Flag == 2) return(SEP_PAIRS);
			return(TOO_LONG);
			}
		if(Planar(FALSE,TRUE) == TRUE) return(TOO_LONG);
		if(Diagram_Main()) return(TOO_LONG);
		}
		
	BadToralBdry = (unsigned char *) NewPtr(NumFaces + 1);
	if(BadToralBdry == NULL) Mem_Error();
	BdryCompFace = (unsigned char *) NewPtr(NumFaces + 1);
	if(BdryCompFace == NULL) Mem_Error();
	PLength = (unsigned int *) NewPtr(sizeof(int)*(NumEdges + 1));
	if(PLength == NULL) Mem_Error();
	PM = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PM == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PM[d] = NULL;	
	PP = (unsigned char **) NewPtr(sizeof(long)*(NumEdges + 1));
	if(PP == NULL) Mem_Error();
	for(d = 1; d <= NumEdges; d++) PP[d] = NULL;
	P_From_Face = (int **) NewPtr(sizeof(long)*(NumFaces + 1));
	if(P_From_Face == NULL) Mem_Error();
	for(d = 0; d <= NumFaces; d++) P_From_Face[d] = NULL;
	PP_From = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_From == NULL) Mem_Error();
	PM_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PM_To == NULL) Mem_Error();
	PP_To = (unsigned char *) NewPtr(sizeof(long)*(NumFaces + 1));
	if(PP_To == NULL) Mem_Error();
	SaveTL = (unsigned char *) NewPtr(NumEdges + 1);
	if(SaveTL == NULL) Mem_Error();
	SaveTR = (unsigned char *) NewPtr(NumEdges + 1);	
	if(SaveTR == NULL) Mem_Error();
	
	InTree = (unsigned char *) NewPtr(NumFaces + 1);
	if(InTree == NULL) Mem_Error();
	MarkedPathsL = (unsigned char *) NewPtr(2*NumEdges + 1);
	if(MarkedPathsL == NULL) Mem_Error();
	PathsInCircuit = (int *) NewPtr(sizeof(int)*(NumFaces + 2));
	if(PathsInCircuit == NULL) Mem_Error();
	FacesVisitedList = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 2));
	if(FacesVisitedList == NULL) Mem_Error();
	FacesVisited = (unsigned char *) NewPtr(sizeof(char)*(NumFaces + 1));
	if(FacesVisited == NULL) Mem_Error();
	SMinCircuitPaths = (unsigned char *) NewPtr(NumEdges + 1);
	if(SMinCircuitPaths == NULL) Mem_Error();
	T1 = (unsigned char *) NewPtr(125);
	if(T1 == NULL) Mem_Error();
	TreeMarkedVertex = (unsigned char *) NewPtr(NumFaces + 1);
	if(TreeMarkedVertex == NULL) Mem_Error();
	TreePathLength = (unsigned int *) NewPtr(sizeof(int)*(NumFaces + 1));
	if(TreePathLength == NULL) Mem_Error();
	TreePreviousPath = (int *) NewPtr(sizeof(int)*(NumFaces + 1));
	if(TreePreviousPath == NULL) Mem_Error();	
	TreePreviousVertex = (unsigned char *) NewPtr(NumFaces + 1);
	if(TreePreviousVertex == NULL) Mem_Error();
	TreeVertex = (unsigned char *) NewPtr(NumFaces + 1);
	if(TreeVertex == NULL) Mem_Error();    	 
	
	BestNewRelator = NULL;
	NewRelator = NULL;
	
	/***************************************************************
		Find the paths, disjoint from the relators, which connect 
		the major faces of the Heegaard diagram.
	***************************************************************/	

	for(i = 1; i <= NumRelators; i++) LR[i] = GetHandleSize((char **) Relators[i]) - 1;
	for(d = 1,max = 0; d <= NumRelators; d++) if(LR[d] > max) max = LR[d];
	T2 = (unsigned char *) NewPtr(max + 2);
	if(T2 == NULL) Mem_Error();	
	for(d = 1; d <= 2*NumEdges; d++) EL[d] = d;
					
	for(ss = 2*NumEdges, NumPaths = 0; ss > 0; ss --)
		{		
		/**************************************************************************************
			Determine which edges of the original diagram are joined by the edge ss of the dual
			diagram.
		**************************************************************************************/	
		
		for(v = c = 0; c + VWG[v] < EL[ss]; v++) c += VWG[v];
		w = EL[ss] - c;
		for(c = ee = 0,vertexLE = d = FV[v]; c < w; c++)
			{
			ee += A[v][d];
			vertexLE = d;
			d = CO[v][d];
			}
		e = ee - 1;
		if(v & 1)
			{	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			if(e) e--;
			else e = V[v] - 1;
			}
		
		p = q = *DualRelators[(v >> 1) + 1] + e;
		q++;
		if(!*q) q = *DualRelators[(v >> 1) + 1];
		if(v & 1)
			{
			tr = *p;
			tl = *q;
			if(tr > 95) tr -= 32;
			else tr += 32;			
			if(tl > 95) tl -= 32;
			else tl += 32;			
			}
		else
			{
			tl = *p;
			tr = *q;
			}	
		
		length	= 0;
		vertex  = v;
		V2 		= vertex;
		edge    = ee % V[v];
		e 		= edge;
		r		= T2;
		
		/**************************************************************************************
			Two relators have come from distinct vertices and are adjacent to each other at
			vertex v. Follow these two relators along until they diverge. The region where
			they are parallel is the "cancellation region".
		**************************************************************************************/	
		
		do
			{
			if(v & 1)
				{
				*r = (v >> 1) + 97;
				w = v - 1;
				}
			else
				{
				*r = (v >> 1) + 65;
				w = v + 1;
				}
			V4 = v;	
			r++;	
			e = OSA[v] - e;
			if(e >= V[v]) e -= V[v];
			length ++;
			if(length > max)
				{			
				Error = 2;				
				goto END;
				}	
			v = FV[w];
			d = A[w][v];
			while(d <= e)
				{
				v = CO[w][v];
				d += A[w][v];
				}	
			if(e == (d - 1))	
				{
				/***********************************************************************
					If e = d - 1, then we have found the end of the cancellation region.
				***********************************************************************/
				
				*r++ = EOS;
				if(V4 & 1)
					V4 -= 1;
				else
					V4 += 1;
				vertexRS = v;
				
				/***********************************************************************
					Determine which edge of the dual diagram corresponds to the end of
					the cancellation region and delete it from the list of available
					edges.
				***********************************************************************/	
				
				for(d = 0,c = 1; d < w; d++) c += VWG[d];
				v = FV[w];
				d = A[w][v];
				while(d <= e)
					{
					c++;
					v = CO[w][v];
					d += A[w][v];
					}
				if(EL[c] == c)
					{
					ss --;
					v = EL[ss];
					EL[ss] = c;
					EL[c] = v;
					}	
				else
					{
					for(d = 1; d < ss && (EL[d] != c); d++) ;
					if(d < ss)
						{
						ss --;
						v = EL[ss];
						EL[ss] = c;
						EL[d] = v;
						}
					}
				if(vertexLE & 1)
					x = (vertexLE >> 1) + 97;
				else
					x = (vertexLE >> 1) + 65;
				V1 = vertexLE;
				V3 = vertexRS;
				
				HSS = r - T2;
				NumPaths ++;
				
				PP[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PP[NumPaths] == NULL) Mem_Error();
				q = PP[NumPaths];	
				p = T2;
				while( (*q++ = *p++) ) ;

				PM[NumPaths] = (unsigned char *) NewPtr(HSS);		
				if(PM[NumPaths] == NULL) Mem_Error();
				Inverse(PP[NumPaths]);
				q = PM[NumPaths];	
				p = PP[NumPaths];
				while( (*q++ = *p++) ) ;
				Inverse(PP[NumPaths]);
				PLength[NumPaths] = length;
				if(tl > 95) tl -= 32;
				else tl += 32;
				SaveTL[NumPaths] = tl;
				SaveTR[NumPaths] = tr;				
							
				/***********************************************************************************
							Identify the initial and terminal faces of this path.
				***********************************************************************************/
				
				for(h = 1,i = FALSE; h <= NumFaces; h++)
					{
					p = Face[h];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V1)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[h];
							if(*q == V2)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}
					
				for(j = 1,i = FALSE; j <= NumFaces; j++)
					{
					p = Face[j];
                	while((x = *p) < VERTICES) 
                		{
                		if(x == V3)
							{
							q = p;
							q++;
							if(*q == VERTICES) q = Face[j];
							if(*q == V4)
								{
								i = TRUE;
								break;
								}	
							}
						p++;
						}
                	if(i) break;	
					}

				PP_From[NumPaths] = h;
				PP_To[NumPaths]   = j;
				PM_To[NumPaths]   = h;
				break;
				}
			e = B[w][v] - e;
			}	
		while(v != vertex || e != edge);	
	}
	
	DisposePtr((char *) T2);
	
	for(i = 1; i <= NumFaces; i++)
		{
		p = Face[i];
		j = 2;
		while(*p++ < VERTICES) j++;
		P_From_Face[i] = (int *)NewPtr(sizeof(int)*j);
		if(P_From_Face[i] == NULL) Mem_Error();
		P_From_Face[i][0] = 1;
		P_From_Face[i][j-1] = Big_Number;
		for(h = 1; h < j-1; h++) P_From_Face[i][h] = 0;	
		}
		
	for(ii = 1; ii <= NumPaths; ii++)
		{
		pp = P_From_Face[PP_From[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = ii;
		pp = P_From_Face[PP_To[ii]];
		while(*pp && *pp != Big_Number) pp++;
		*pp = -ii;	
		}
		
	/***************************************************************************************
			Examine the boundary components of this manifold. If F is a boundary component, 
		and F has at most two boundary simple closed curves, the only possible length 
		reducing replacements are bandsums, which have already been checked. So F must have 
		more than two boundary simple closed curves. If F is such a punctured torus, add F 
		to a list of boundary components to be checked. (Note, if F has genus greater than 
		one and F has more than two boundary simple closed curves, then Heegaard does not 
		currently check F.)		
	***************************************************************************************/
		
    for(i = 1; i <= NumFaces; i++) BdryCompFace[i] = FALSE;                
    CompNum = 0;
    NumGenusZeroBdryComps 	= 0;
    NumBadToralBdryComps 	= 0;
    NumBadNonToralBdryComps = 0;
    while(1)
        {
        for(i = 1; BdryCompFace[i] && (i <= NumFaces); i++) ;
  		if(i > NumFaces) break;
        CompNum ++;                        
        BdryCompFace[i] = CompNum;
        NumCompFaces = 1;
        NumCompPaths = 0;
        for(j = 0; j < NumRelators; j++) T1['A'+ j] = T1['a'+ j] = 0;
        for(rrr = UpDate,*rrr = i,ppp = rrr + 1; rrr < ppp; rrr++)
            {
            i = *rrr;
            for(h = 1; (k = P_From_Face[i][h]) != Big_Number; h++)
                {
                NumCompPaths++;
                T1[SaveTL[abs(k)]]++;
                T1[SaveTR[abs(k)]]++;
                if(k > 0)
                	{
                	NewFace = PP_To[k];
                	if(!BdryCompFace[NewFace])
                		{
                		NumCompFaces++;
                		BdryCompFace[NewFace] = CompNum;
                		*ppp++ = NewFace;
                		}
                	}
                 if(k < 0)
                	{
                	NewFace = PM_To[-k];
                	if(!BdryCompFace[NewFace])
                		{
                		NumCompFaces++;
                		BdryCompFace[NewFace] = CompNum;
                		*ppp++ = NewFace;
                		}
                	}                
                }
            }
        NumCompPaths /= 2;
		for(i = 0,NumCompBdries = 0; i < NumRelators; i++) 
			{
			if(T1['A'+i]) NumCompBdries++;
			if(T1['a'+i]) NumCompBdries++;			
			}
		Chi = NumCompFaces - NumCompPaths + NumCompBdries;
		if(Chi == 2) NumGenusZeroBdryComps ++;
		if((Chi == 0) && (NumCompBdries > 2))
			{
			BadToralBdry[NumBadToralBdryComps] = CompNum;
			NumBadToralBdryComps ++;
		    }
		if((Chi < 0) && (NumCompBdries > 2)) NumBadNonToralBdryComps ++;    		    
        }   
    if((Flag == FALSE || Flag == 2) && CompNum == NumGenusZeroBdryComps)
    	{
    	if(CompNum == 1) 	RRV = 4;
    	if(CompNum > 1)		RRV = 5;
		goto END;
    	} 
    	
   /********************************************************************
   		if(Flag == FALSE) Check if there is a length-reducing bandsum.
   *********************************************************************/ 
  
	if(Flag == FALSE || Flag == 2) for(i = 1; i <= NumPaths; i++)
		{
		if(SaveTL[i] == SaveTR[i]) continue;
		if(abs(SaveTL[i] - SaveTR[i]) == 32) continue;
		x = SaveTL[i];
		if(x < 94)
			x -= 64;
		else
			x -= 96;	
		if(2*PLength[i] >= GetHandleSize((char **) OutRelators[x])) 
			{
			RRV = 6;
			goto END;
			}
		x = SaveTR[i];
		if(x < 94)
			x -= 64;
		else
			x -= 96;	
		if(2*PLength[i] >= GetHandleSize((char **) OutRelators[x])) 
			{
			RRV = 6;
			goto END;
			}
		}
		   	 
	P_From_Face[0] = (int *) NewPtr(sizeof(int)*(NumPaths + 2));
	if(P_From_Face[0] == NULL) Mem_Error();
	
	SFoundShorterRelator = FALSE;
	
	/*********************************************************************************************
		Take each punctured torus boundary component with more than two simple closed curve 
		boundaries in turn and search for the minimal length simple closed curve, disjoint 
		from the relators, which lies on that punctured torus boundary component.
	**********************************************************************************************/	
	
	for(i = 1; i <= NumFaces; i++) FacesVisited[i] = FALSE;
	MaxLengthReduction = 0;
	for(mm = 0, NumCircuitsFound = 0; mm < NumBadToralBdryComps; mm ++)
	{
	CurrentBdryComp = BadToralBdry[mm];
	MinCircuitLength = Big_Number;
	NonSepCircuit = FALSE;	
	for(i = 1; i <= NumFaces; i++)
		{
		if(BdryCompFace[i] != CurrentBdryComp) continue;
		InitialFace = i;
		TerminalFace = i;
		NumPathsInCircuit = 0;
		CumulativeLength = 0;
		FacesVisitedList[1] = InitialFace;
		while(1)
			{
			h = P_From_Face[TerminalFace][0];
			P_From_Face[TerminalFace][0] ++;
			ii = P_From_Face[TerminalFace][h];
			if(ii == Big_Number)
				{
				/***********************************************************************************  
						We've reached a dead end. No new path from the current terminal face leads 
					to a new face. Clear info for the current terminal face and reset the terminal 
					face to the previous face. 	
				***********************************************************************************/ 
				
				P_From_Face[TerminalFace][0] = 1;
				FacesVisited[TerminalFace] = FALSE;
				if(NumPathsInCircuit == 0) 
					{
					CumulativeLength = 0;
					break;
					}
				CumulativeLength -= PLength[abs(PathsInCircuit[NumPathsInCircuit])];
				NumPathsInCircuit --;
				TerminalFace = FacesVisitedList[NumPathsInCircuit + 1];	
				continue;
				}
			if(ii != Big_Number)
				{
				if(ii > 0) PossibleNewTerminalFace = PP_To[ii];
				if(ii < 0) PossibleNewTerminalFace = PM_To[-ii];
				if(PossibleNewTerminalFace < InitialFace) continue;
				if(PossibleNewTerminalFace == InitialFace)
					{
					if((NumPathsInCircuit == 0) && (ii < 0)) continue;
					if((NumPathsInCircuit > 0) && (ii == -PathsInCircuit[1])) continue;
					if((NumPathsInCircuit > 1) && (TerminalFace < FacesVisitedList[2])) continue;
					if((NumPathsInCircuit == 1) && (abs(ii) < abs(PathsInCircuit[1]))) continue;
					CumulativeLength += PLength[abs(ii)];
					if(CumulativeLength >= MinCircuitLength) 
						{
						CumulativeLength -= PLength[abs(ii)];
						continue;
						}				
					NumPathsInCircuit ++;
					PathsInCircuit[NumPathsInCircuit] = ii;
					NumCircuitsFound ++;
															
 					/*****************************************************
 						Check whether this circuit is non-separating.
 					******************************************************/	
 
					for(j = 0; j < NumRelators; j++) T1['A'+j] = T1['a'+j] = FALSE;
					for(j = 1; j <= NumPathsInCircuit; j++)
						{
						k = PathsInCircuit[j];
						if(k > 0) T1[SaveTL[k]] = 'l';
						if(k < 0) T1[SaveTR[-k]] = 'l';
						}
					for(j = 1, NonSepCircuit = FALSE; j <= NumPathsInCircuit; j++)	
						{
						k = PathsInCircuit[j];
						if(k > 0) 
							{
							if(T1[SaveTR[k]] == 'l')
								{
								NonSepCircuit = TRUE;
								break;
								}
							T1[SaveTR[k]] = 'r';	
							}
						if(k < 0) 
							{
							if(T1[SaveTL[-k]] == 'l')
								{
								NonSepCircuit = TRUE;
								break;
								}
							T1[SaveTL[-k]] = 'r';	
							}
						}
											
 					if(NonSepCircuit == FALSE) 
 						{						
						for(j = 0; j <= 2*NumPaths; j++) MarkedPathsL[j] = FALSE;
						for(j = 1; j <= NumPathsInCircuit; j++) MarkedPathsL[NumPaths+PathsInCircuit[j]] 
							= MarkedPathsL[NumPaths-PathsInCircuit[j]] = 2;
						do
							{
							for(j = 1,FoundNew = FALSE; j <= NumPaths; j++) 
								{
								if(MarkedPathsL[NumPaths + j] == 2) continue;
								STLj = SaveTL[j];
								STRj = SaveTR[j];
								if(T1[STLj] == T1[STRj]) continue;
								if(T1[STLj] && T1[STRj])
									{
									NonSepCircuit = TRUE;
									break;
									}
								if(!T1[STLj])
									{
									T1[STLj] = T1[STRj];
									FoundNew = TRUE;
									}
								if(!T1[STRj])
									{
									T1[STRj] = T1[STLj];
									FoundNew = TRUE;
									}			
								}
							}
						while((NonSepCircuit == FALSE) && (FoundNew == TRUE));
						}										

					if(NonSepCircuit == TRUE)
						{
						/***********************************************************
								Save a copy of this potentially minimal circuit in 
							Paths_In_Circuit[ ] to P_From_Face[0][ ]. Then it can be
							recovered later if it is indeed minimal.
						***********************************************************/	
						for(j = 1; j <= NumPathsInCircuit; j++) 
							P_From_Face[0][j] = PathsInCircuit[j];
						P_From_Face[0][j] = 0;
						}					
							
					if(NonSepCircuit) MinCircuitLength = CumulativeLength;
					CumulativeLength -= PLength[abs(PathsInCircuit[NumPathsInCircuit])];
					NumPathsInCircuit --;					
					continue;	
					}		
		
				if((PossibleNewTerminalFace > InitialFace) && (FacesVisited[PossibleNewTerminalFace] == FALSE) 
					&& (CumulativeLength + PLength[abs(ii)] < MinCircuitLength))		
					{
					TerminalFace = PossibleNewTerminalFace;
					NumPathsInCircuit ++;
					PathsInCircuit[NumPathsInCircuit] = ii;
					FacesVisited[TerminalFace] = TRUE;
					FacesVisitedList[NumPathsInCircuit + 1] = TerminalFace;
					CumulativeLength += PLength[abs(ii)];
					}
				}			
			}	
		}
				
	if(NonSepCircuit == TRUE)
		{		
		/***************************************************************************
			Use the copy of PathsInCircuit[ ] saved in P_From_Face[0][ ] to restore
			PathsInCircuit[ ], FacesVisitedList[ ], and NumPathsInCircuit. 
		***************************************************************************/
		
		for(j = 1, NumPathsInCircuit = CumulativeLength = 0; ; j++)
			{
			if(P_From_Face[0][j] == 0)
				{
				FacesVisitedList[1] = FacesVisitedList[j];
				break;
				}
			NumPathsInCircuit ++;
			k = P_From_Face[0][j];
			CumulativeLength +=	PLength[abs(k)];
			PathsInCircuit[j] = k;
			if(k > 0) FacesVisitedList[j+1] = PP_To[k];
			if(k < 0) FacesVisitedList[j+1] = PM_To[-k];
			}
					
		/*********************************************************************************
			Get VIn and VOut for each face of the circuit. Also, for each face which the 
			circuit traverses, determine for each path P leaving that face whether P 
			leaves the face from the left side or the right side of the circuit.
		*********************************************************************************/

		for(j = 0; j <= 2*NumPaths; j++) MarkedPathsL[j] = FALSE;
		for(j = 1; j <= NumPathsInCircuit; j++) MarkedPathsL[NumPaths+PathsInCircuit[j]] 
			= MarkedPathsL[NumPaths-PathsInCircuit[j]] = 2;
													
		P_From_Face[0][0] = 1;
		
		for(j = 1,NumLPaths = 0; j <= NumPathsInCircuit; j++)
			{
			if(j == 1) 	k = PathsInCircuit[NumPathsInCircuit];
			else 		k = PathsInCircuit[j-1];
			if(k > 0) V1 = *PM[k];
			else V1 = *PP[-k];
			k = PathsInCircuit[j];
			if(k > 0) V2 = *PP[k];
			else V2 = *PM[-k];						
			pp = P_From_Face[FacesVisitedList[j]];
			pp ++;
			while((k = *pp++) != Big_Number)
				{
				if(k > 0) V3 = *PP[k];
				else V3 = *PM[-k];
				if(V3 == V1 || V3 == V2) continue;								
				for(h = 0; (V4 = Face[FacesVisitedList[j]][h]) < VERTICES; h++)
					{
					if(V4 & 1) x = V4/2 + 97;
					else x = V4/2 + 65;
					if(x == V1 || x == V2 || x == V3) break;
					}
				for(++h; (V4 = Face[FacesVisitedList[j]][h]) < VERTICES; h++)
					{
					if(V4 & 1) y = V4/2 + 97;
					else y = V4/2 + 65;
					if(y == V1 || y == V2 || y == V3) break;
					}
				if(x == V1 && y == V2)  LSidePath = FALSE;
				if(x == V1 && y == V3)  LSidePath = TRUE;
				if(x == V2 && y == V1)  LSidePath = TRUE;
				if(x == V2 && y == V3)  LSidePath = FALSE;
				if(x == V3 && y == V1)  LSidePath = FALSE;
				if(x == V3 && y == V2)  LSidePath = TRUE;
				if(LSidePath == TRUE)
					{
					P_From_Face[0][++NumLPaths] = k;
					MarkedPathsL[NumPaths - k] = 3;					
					}
				else
					{
					MarkedPathsL[NumPaths + k] = 3;
					MarkedPathsL[NumPaths - k] = 1;				
					}	
				}
			}
		P_From_Face[0][++NumLPaths] = Big_Number;
		
		/*******************************************************************
			Find the path of shortest total length which connects the left
			and right sides of our minimal length non-separating circuit.
		*******************************************************************/
	
		TreeVertex[0] = 0;
		TreePreviousPath[0] = 0;
		TreePathLength[0] = 0;
		TreeSize = 1;
		for(j = 1; j <= NumFaces; j++) InTree[j] = FALSE;
		InTree[0] = TRUE;
		while(1)
			{
			for(j = 0,TreeTrialMinPathLength = Big_Number; j < TreeSize; j++)
				{
				pp = P_From_Face[TreeVertex[j]];
				pp ++;
				while((k = *pp++) != Big_Number)
					{
					if(MarkedPathsL[NumPaths + k] > 1) continue;
					if((TreePathLength[j] + PLength[abs(k)]) < TreeTrialMinPathLength)
						{
						TreeTrialMinPathLength = TreePathLength[j] + PLength[abs(k)];
						ChosenPath = k;
						}
					}
				}
			if(ChosenPath > 0) MyFace = PP_To[ ChosenPath];
			if(ChosenPath < 0) MyFace = PM_To[-ChosenPath];							
			if(InTree[MyFace])
				{
				if(MarkedPathsL[NumPaths + ChosenPath] == FALSE) 
					MarkedPathsL[NumPaths + ChosenPath] = 4;
				if(MarkedPathsL[NumPaths - ChosenPath] == FALSE) 
					MarkedPathsL[NumPaths - ChosenPath] = 4;
				continue;
				}
			TreeVertex[TreeSize] = MyFace;
			InTree[MyFace] = TRUE;
			TreePreviousPath[TreeSize] = -ChosenPath;
			TreePathLength[TreeSize] = TreeTrialMinPathLength;							
			if(MarkedPathsL[NumPaths + ChosenPath] == FALSE) 
				MarkedPathsL[NumPaths + ChosenPath] = 3;
			if(MarkedPathsL[NumPaths - ChosenPath] == FALSE) 
				MarkedPathsL[NumPaths - ChosenPath] = 3;																
			if(MarkedPathsL[NumPaths + ChosenPath] == 1)
				{				
				for(j = 1; j <= NumPaths; j++) SMinCircuitPaths[j] = FALSE;
				for(j = 1; j <= NumPathsInCircuit; j++) SMinCircuitPaths[abs(PathsInCircuit[j])] = TRUE;
	
				MyFace = TreeVertex[TreeSize];
				for(j = TreeSize; j > 0; j --) if(TreeVertex[j] == MyFace)
					{
					k = TreePreviousPath[j];
					SMinCircuitPaths[abs(k)] = TRUE;
					if(k > 0) MyFace = PP_To[k];
					if(k < 0) MyFace = PM_To[-k];
					}			
				break;	
				}
			TreeSize++;	
			}
		
		/***************************************** 
			Set up DRA[ ][ ] for Find_Flow_D().
			(Note Vertices gets changed here.)	
		******************************************/	
		
		Vertices = 2*NumRelators + 1;
	    for(i = 0; i < Vertices; i++)
    	for(j = 0; j < Vertices; j++) DRA[i][j] = 0;		
		for(j = 1; j <= NumPaths; j++)
			{
			if(SMinCircuitPaths[j])
				{
				i = Vertices - 1;
				x = SaveTL[j];
				x = x << 1;
            	if(x < 194) x -= 130;
           		else x -= 193;
            	DRA[i][x] += PLength[j];
            	x = SaveTR[j];
				x = x << 1;
            	if(x < 194) x -= 130;
           		else x -= 193;
            	DRA[i][x] += PLength[j];
				}
			else
				{
				x = SaveTL[j];
				x = x << 1;
            	if(x < 194) x -= 130;
           		else x -= 193;
           		y = SaveTR[j];
				y = y << 1;
            	if(y < 194) y -= 130;
           		else y -= 193;
           		DRA[x][y] += PLength[j];
				}			
			}
		for(i = 0; i < Vertices - 1; i++)
		for(j = i + 1; j < Vertices; j++)
			{
			DRA[i][j] += DRA[j][i];
			DRA[j][i] = DRA[i][j];
			}	

		/*********************************************
			Finally, set up VA[ ] for Find_Flow_D().
		**********************************************/
	
		for(h = 0; h < NumRelators; h++)
			{
			k = 2*h;
			for(i = j = 0; i <= 2*NumRelators; i++) j += DRA[k][i]; 
			VA[h] = j;
			}								
		
		Find_Flow_D(Flag);
			 			
		}
	}
	
	if(!SFoundShorterRelator && Batch == 8 && H_Results != NULL) fprintf(H_Results,"\n\n%s <-- PM.",PresName); 
	if(SFoundShorterRelator)
		{
		if(Flag == FALSE) goto END;
		Length -= MaxLengthReduction;
		Temp = OutRelators[RelatorReplaced];
		OutRelators[RelatorReplaced] = BestNewRelator;
		BestNewRelator = Temp;		
		for(i = 1; i <= NumRelators; i++)
            {
            Temp           	= Relators[i];
            Relators[i]    	= OutRelators[i];
            OutRelators[i] 	= Temp;
            }		
		}
END:
	for(j = 1; j <= NumPaths; j++) 
		{
		if(PM[j] != NULL) DisposePtr((char *) PM[j]);
		if(PP[j] != NULL) DisposePtr((char *) PP[j]);		
		}
	
	for(j = 0; j <= NumFaces; j++)  if(P_From_Face[j]) DisposePtr((int *) P_From_Face[j]);
	if(BestNewRelator != NULL)		DisposeHandle((char **) BestNewRelator);	
	if(BadToralBdry != NULL)		DisposePtr((unsigned char *) BadToralBdry);
	if(BdryCompFace != NULL)		DisposePtr((unsigned char *) BdryCompFace);	
	if(PLength != NULL)				DisposePtr((unsigned int *) PLength);
	if(PM != NULL) 					DisposePtr((unsigned char **) PM);
	if(PP != NULL) 					DisposePtr((unsigned char **) PP);	
	if(P_From_Face != NULL) 		DisposePtr((int **) P_From_Face);
	if(PP_From != NULL) 			DisposePtr((unsigned char *)  PP_From);
	if(PM_To != NULL) 				DisposePtr((unsigned char *)  PM_To);	
	if(PP_To != NULL) 				DisposePtr((unsigned char *)  PP_To);	
	if(SaveTL != NULL)				DisposePtr((unsigned char *) SaveTL);	
	if(SaveTR != NULL)				DisposePtr((unsigned char *) SaveTR);		


	if(InTree != NULL)				DisposePtr((unsigned char *) InTree);
	if(MarkedPathsL != NULL)		DisposePtr((unsigned char *) MarkedPathsL);		
	if(PathsInCircuit != NULL) 		DisposePtr((int *) PathsInCircuit);	
	if(FacesVisitedList != NULL) 	DisposePtr((unsigned char *) FacesVisitedList);	
	if(FacesVisited != NULL) 		DisposePtr((unsigned char *) FacesVisited);	
	if(SMinCircuitPaths != NULL)  	DisposePtr((unsigned char *) SMinCircuitPaths);	
	if(T1 != NULL)					DisposePtr((unsigned char *) T1);
	if(TreeMarkedVertex != NULL)	DisposePtr((unsigned char *) TreeMarkedVertex);
	if(TreePathLength != NULL)		DisposePtr((unsigned int *) TreePathLength);	
	if(TreePreviousPath != NULL)  	DisposePtr((int *) TreePreviousPath);		
	if(TreePreviousVertex != NULL) 	DisposePtr((unsigned char *) TreePreviousVertex);
	if(TreeVertex != NULL)			DisposePtr((unsigned char *) TreeVertex);	
	
	SLength = SSSSLength;
	
	if(RRV > 3) return(RRV);
	
	if(SFoundShorterRelator) 
		return(1);
	else
		{
		if(NumBadNonToralBdryComps == 0) return(2);  /* This Heegaard diagram is pseudo-minimal. */
		if(NumBadNonToralBdryComps  > 0) return(3);  /* This Heegaard diagram is quasi-pseudo-minimal. */
		}
return(0);			
}

int Find_Flow_D(char Flag)
{
    /******************************************************************************************
		
    ******************************************************************************************/
    
    char			FoundShorterRelator;
    
    unsigned char	c,
    				MyFace,
    				PossiblePaths,
    				*pp,
    				*qq,
    				x;
    
    int				CurrentPath,
    				m,
    				MinJ,
    				NextPath;
            
    unsigned int   	EntryVertexNum,
    				Flow,
    				h,
    				i,
                	j,
                	k,
                    max,
                    MaxFlow,
                    min,
                    NewRelatorLength,
                    S[VERTICES],
                    Sink,
                    Source,
                    *p,
                    *q,
                    *r;                      
   
    if(NumRelators == 0) return(TOO_LONG);
    	     
    for(i = 0; i < Vertices; i++)
        {
        for(j = k = 0; j < Vertices; j++) if(DRA[i][j])
            {
            AJ3[i][k] = j;
            k++;
            }
        AJ3[i][k] = VERTICES;
        }        
    for(i = 0; i < Vertices; i++) XX[i] = FALSE;
    XX[Vertices - 1] = TRUE;
    for(r = UpDate,*r = Vertices - 1,p = r + 1; r < p; r++) 
    	{
    	i = *r;
    	for(h = 0; (j = AJ3[i][h]) < VERTICES; h++)
    		{
    		if(i == j) continue;
    		if(XX[j] == FALSE) 
    			{
    			XX[j] = TRUE;
    			*p++ = j;
    			}
    		}
    	} 
    	 
  	FoundShorterRelator = FALSE;
  	     
    for(k = 0; k < Vertices - 1; k += 2)
        {
		if(XX[k] && XX[k + 1]) 
			/******************************************************************** 
							Vertex k and vertex k+1 both lie in T.
				Look for a minimal cut in D separating vertex k and vertex k+1. 
			*********************************************************************/
			{
			Source = k;
			Sink = k + 1;
			}		
		if(XX[k] && !XX[k + 1]) 
			/******************************************************************* 
					Vertex k lies in T, vertex k+1 does not lie in T.
				Look for a minimal cut in D separating vertex k and vertex C.	
			********************************************************************/	
			{
			Source = k;
			Sink = Vertices - 1;
			}		
		if(!XX[k] && XX[k + 1])
			/********************************************************************
					Vertex k+1 lies in T, vertex k does not lie in T.
				Look for a minimal cut in D separating vertex k+1 and vertex C.	
			*********************************************************************/
			{
			Source = k + 1;
			Sink = Vertices - 1;
			}
		if(!XX[k] && !XX[k + 1]) continue; /* Neither vertex k or vertex k+1 lie in T. */
			                       
        MaxFlow          	= VA[k >> 1];        
        Flow             	= DRA[Source][Sink];
        DRA[Source][Sink]  	= 0;
        DRA[Sink][Source] 	*= 2;
           
        while(MaxFlow)
            {        
            for(i = 0,p = ZZ,q = InQueue; i < Vertices; i++,p++,q++) *p = *q = 0;
            ZZ[Sink] = INFINITE;
            InQueue[Source] = TRUE; 
            /********************************************************  
				(Setting InQueue[Source] = TRUE prevents unnecessary 
				attempts to change paths from vertices to the Sink 
				to paths which pass through the Source.)           
			*********************************************************/
                                        
            for(r = UpDate,*r = Sink,p = r + 1; r < p; r++)
                {
                /******************************************************************************
                    ZZ[j] holds the current value of a maximal width path of edges from vertex
                    j to the Sink. S[j] is the neighbor of vertex j to which this path proceeds
                    from vertex j. UpDate is a queue of vertices whose width of path to the 
                    sink has been increased and whose neighbors need to be examined to see if 
                    there is a path to the sink of greater width than their current path to the
                    Sink. InQueue[ ] is used to prevent redundant entries of a vertex in UpDate.
                        Note that there is no point in updating paths from vertices to the
                    Sink unless the updated path has width greater than the current width of
                    the path from Source to Sink. Hence no updating is done unless the path has
                    width greater than the current value of ZZ[Source].
                ******************************************************************************/
                
                i = *r;
                InQueue[i] = FALSE;
                max = ZZ[i];
                if(max > ZZ[Source]) for(q = AJ3[i]; (j = *q) < VERTICES; q++)
                    {
                    if(max > ZZ[j])
                        {
                        if(DRA[j][i] < max)
                            min = DRA[j][i];
                        else
                            min = max;    
                        if(min > ZZ[j])    
                            {
                            /******************************************************************
                                (Note : DRA[j][i] gives the current number of edges available 
                            for a path from vertex j to vertex i.)
                                There is a new path of 'min' parallel edges from vertex j to 
                            the Sink which leaves vertex j and goes to vertex i. And 'min' is
                            greater than the current flow ZZ[j] from vertex j to the Sink.
                                Increase the flow from vertex j to the sink to the value 'min', 
                            and set S[j] equal to i. If 'min' is greater than the current flow 
                            from Source to Sink, and the flows from neighbors of vertex j to j
                            are not already slated to be updated, set InQueue[j] 'TRUE' so we 
                            will check to see if the flow from neighboring vertices of vertex 
                            j can be increased. Also enter vertex j in the UpDate queue.
                                (The function of InQueue[ ] is to keep a vertex from being
                            entered more than once in the array UpDate[ ] between times it is
                            reexamined.)
                            ******************************************************************/
                            
                            ZZ[j] = min;
                            S[j] = i;
                            if(!InQueue[j] && min > ZZ[Source])
                                {
                                InQueue[j] = TRUE;
                                *p++ = j;
                                }
                            }
                        }
                    }
                }                                                    
            max = ZZ[Source];
            Flow += max;
            if(Flow >= MaxFlow) break;
            if(max == 0) break;
            i = Source;
            while(i != Sink)
                {
                /******************************************************************************
                    We have found a path of 'max' parallel edges from Source to Sink. Update
                    the entries of DRA[ ][ ] to reflect this.
                ******************************************************************************/
                j = S[i];
                DRA[i][j] -= max;                                                                
                DRA[j][i] += max;                                    
                i = j;
                }                                                
            }
                                                                    
        /**************************************************************************************
                If MaxFlow is greater than Flow, then the flow from source to sink is less 
                than the valence of the source. Hence there is a shorter relator available.
        **************************************************************************************/
        
        if(MaxFlow > Flow)
        	{
        	FoundShorterRelator  = TRUE;
        	SFoundShorterRelator = TRUE;
       		if(Flag == FALSE) return(1);
        	if(ZZ[Vertices - 1]) for(i = 0; i < NumRelators; i++)
        		{
        		if(ZZ[2*i]) T1['A' + i] = TRUE;
        		else T1['A' + i] = FALSE;
        		if(ZZ[2*i + 1]) T1['a' + i] = TRUE;
        		else T1['a' + i] = FALSE;
        		}
        	if(ZZ[Vertices - 1] == 0) for(i = 0; i < NumRelators; i++)
        		{
        		if(ZZ[2*i]) T1['A' + i] = FALSE;
        		else T1['A' + i] = TRUE;
        		if(ZZ[2*i + 1]) T1['a' + i] = FALSE;
        		else T1['a' + i] = TRUE;
        		}
			for(i = 0; i <= 2*NumPaths; i++) MarkedPathsL[i] = FALSE;
        	for(i = 1; i <= NumPaths; i++)
        		{
        		if(SMinCircuitPaths[i])
        			{
        			if(!T1[SaveTL[i]]) MarkedPathsL[NumPaths + i] = TRUE;
        			if(!T1[SaveTR[i]]) MarkedPathsL[NumPaths - i] = TRUE;
        			}
        		else
        			{
        			if( T1[SaveTL[i]] && !T1[SaveTR[i]]) MarkedPathsL[NumPaths - i] = TRUE;
					if(!T1[SaveTL[i]] &&  T1[SaveTR[i]]) MarkedPathsL[NumPaths + i] = TRUE;        			
        			}
        		}
        		
	     	for(i = 1,NewRelatorLength = 0; i <= NumPaths; i++) 
        		{
        		if(MarkedPathsL[NumPaths + i]) NewRelatorLength += PLength[i];
        		if(MarkedPathsL[NumPaths - i]) NewRelatorLength += PLength[i];
        		}
      	
        	if(NewRelator != NULL) DisposePtr((unsigned char *) NewRelator);
        	NewRelator = (unsigned char *) NewPtr(NewRelatorLength + 1);
        	if(NewRelator == NULL) Mem_Error();				
       		qq = NewRelator;
       		
         	for(i = 1; i <= NumPaths; i++) 
        		{
        		if(MarkedPathsL[NumPaths + i]) 
        			{
					CurrentPath = i;
					break;
        			}
        		if(MarkedPathsL[NumPaths - i])
        			{
					CurrentPath = -i;
					break;
        			}	
        		}
        		    		 
			while(1)
				{
				MarkedPathsL[NumPaths + CurrentPath] = 2;    	
				if(CurrentPath > 0) 
					{
					MyFace = PP_To[CurrentPath];
					x = *PM[CurrentPath];
					pp = PP[CurrentPath];
					while( (*qq++ = *pp++) )  ;
					qq--;
					}
				if(CurrentPath < 0)
					{
					MyFace = PM_To[-CurrentPath];
					x = *PP[-CurrentPath];
					pp = PM[-CurrentPath];
					while( (*qq++ = *pp++) )  ;
					qq--;					
					}
				
				for(i = 1, PossiblePaths = 0; (m = P_From_Face[MyFace][i]) != Big_Number; i++) 
				if(MarkedPathsL[NumPaths + m] == 1)
					{
					PossiblePaths++;
					NextPath = m;
					if(PossiblePaths > 1) break;
					}
				if(PossiblePaths == 0) break;		
				if(PossiblePaths > 1)
					{
					for(j = 0; (h = Face[MyFace][j]) < VERTICES; j++)
						{
						if(h & 1)
							c = h/2 + 97;
						else
							c = h/2 + 65;
						if(x == c) break;	
						}
					EntryVertexNum = j;
				
					for(i = 1,MinJ = Big_Number; (m = P_From_Face[MyFace][i]) != Big_Number; i++) 
					if(MarkedPathsL[NumPaths + m] == 1)
						{
						if(m == -CurrentPath) continue;
						if(m > 0) x = *PP[m];
						if(m < 0) x = *PM[-m];
						for(j = 0; (h = Face[MyFace][j]) < VERTICES; j++)
							{
							if(h & 1)
								c = h/2 + 97;
							else
								c = h/2 + 65;
							if(x == c) break;	
							}
						if(j < EntryVertexNum) j += VERTICES;
						if(j < MinJ)
							{
							MinJ = j;
							NextPath = m;
							}			
						}					
					}
				CurrentPath = NextPath;		
				}
											
       		LR[0] = GetHandleSize((char **) OutRelators[k/2 + 1]) - 1;
	       	if((LR[0] - Flow) > MaxLengthReduction)
        		{        		
        		MaxLengthReduction = LR[0] - Flow;
        		if(BestNewRelator != NULL) DisposeHandle((char **) BestNewRelator);
        		BestNewRelator = (unsigned char **) NewHandle(GetPtrSize((char *)NewRelator));
        		if(BestNewRelator == NULL) Mem_Error();
        		pp = NewRelator;
        		qq = *BestNewRelator;
        		while( (*qq++ = *pp++))  ;
        		RelatorReplaced = k/2 + 1;
        		SCurrentBdryComp = CurrentBdryComp;
        		}        		        		
        	if(Batch == 8 && H_Results != NULL) fprintf(H_Results,"\n\n%s <-- Not PM!",PresName);				
			}
			
		for(i = 1; i < Vertices; i++)
		for(p = AJ3[i]; (j = *p) < i; p++)
		DRA[i][j] = DRA[j][i] = (DRA[i][j] + DRA[j][i]) >> 1;
		} 
	if(NewRelator != NULL) DisposePtr((unsigned char *) NewRelator);
    NewRelator = NULL;	                                                       				
	return(0);	
}     