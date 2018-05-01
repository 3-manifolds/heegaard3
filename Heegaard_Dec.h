
extern FILE
	*H_Results,
	*H_Results_2,
	*Gvizdata,
	*input_relators;
	
extern char
	Check_for_1_HS,
	Check_for_1_HS2,
	Check_If_HS_Rep,
	CheckHSReps,
	CheckHS0Length,
	DisAmbigFlag,
	*ER,
	FoundBigSF,
	FoundEssentialTorus,
	FoundSF,
	FoundFiniteSF,
	SPM_Flag;
	
extern unsigned char
    B5PrintBdryComps,
    B5PrintDualRelators,
    B5PrintPaths,
    B5TestSimpleCircuits,
    B10B11Finite,
    B10B11HSReps,
    B10B11Recognized,
    B10B11SaveOnlyHS1P1,
    B14B15PrintPres,
    B51RewriteDualRelators,
    Batch,
    *BCF,
    *BCWG,		
    BPrintAnnulusData,
    BPrintNotConnectedData,	
    BreadthFirstSearch,	
    *CBC[MAXNUMCOMPONENTS],	
    *CO[VERTICES],
    **CD_Surgery_Rel[MAXNUMRELATORS + 1],	
    **Copy_Of_Input[MAXNUMRELATORS + 1],
    **Copy_Of_Rel_1[MAXNUMRELATORS + 1],
    **Copy_Of_Rel_2[MAXNUMRELATORS + 1],
    **Copy_Of_Rel_3[MAXNUMRELATORS + 1],			
    *CS,
    *CSF,
    *DD,
    *DeletedEdgePtr,
    *DeletedEdges,
    **DelRelators[MAXNUMRELATORS + 1],
    DepthFirstSearch,	
    **DualRelators[MAXNUMRELATORS + 1],
    **Exp_Surgery_Rel[MAXNUMRELATORS + 1],	
    *Face[2*VERTICES],
    *FV,
    *GBC,
    GoingDown,
    GoingUp,
    GoingUpDown,
    *HNL,
    *Inst,
    **KorLRelators[MAXNUMRELATORS + 1],
    *Low,
    *LStack,	
    *MM[VERTICES],	
    *N1H,
    *NCS,
    *NXMG,	
    *NS1XD2,
    *NS1XS2,
    *Num,
    NumAEXPS,
    NumBEXPS,
    *OnLStack,		
    **OutRelators[MAXNUMRELATORS + 1],
    *PresName,
    *QPM,			
    **Relators[MAXNUMRELATORS + 1],
    *RWR[MAXNUMDUPS], 
    *SatEdgeList1,
    *SatEdgeList2,	
    *SComp,	
    **SETR1,
    **SETR2,
    **SETR3,
    **SETR4,
    *SepVertexList,	
    *SinkSet,	
    ***SLR[MAX_SAVED_LEVELS],
    ****SLP,
    ****SMGP,
    ****SUR,
    *T[(VERTICES)/2],
    *TC[VERTICES],	
    **Temp1,
    **Temp2,
    **Temp3,
    **Temp4,
    **Temp5,
    **Temp6,
    **Temp7,
    **Temp8,
    **Temp9,
    **Temp10,
    **Temp11,
    **Temp12,
    **Temp13,
    **Temp14,
    **Temp15,
    **Temp16,
    **TopOfChain[MAXNUMRELATORS + 1],	
    *TP,
    TestRealizability1,
    TestRealizability2,
    TestRealizability3,
    TestRealizability4,
    **WirtingerL[MAXNUMRELATORS + 1],
    **WirtingerM[MAXNUMRELATORS + 1];

extern int
	*Alphas,
	*BDY,
	BdryData,
	*Betas,
	Betti_Number,
	Boundary,
	Compute_Stabilizers,
	Connected,
	CopyNumGenerators,
	CopyNumRelators,
	Count,
	CurrentComp,
	CycleDiagrams,
	Delete_Only_Short_Primitives,
	Did_Cutting_Disk_Surgery,	
	Did_Exponent_Surgery,
	Do_Not_Reduce_Genus,
	DrawingDiagrams,
	EmtyRel,
	EXPA1_SF[6],
	EXPA2_SF[6],
	EXPB1_SF[6],
	EXPB2_SF[6],
	Find_All_Min_Pres,	
	*Flags,
	FormBandsums,
	FoundPower,
	FoundPrimitive,
	*GB[VERTICES],
	HS_Rep_NumGens,
	*InPS,
	Input,
	Knot_Or_Link,
	Level_Interrupt,	
	MajorVert,
	Micro_Print,
	Micro_Print_F,
	Min_Num_Generators,
	Modified_Init_Pres,
	NEXA1_SF[6],
	NEXA2_SF[6],
	NEXB1_SF[6],
	NEXB2_SF[6],	
	*NG,
	NG_TOC,
	NGV2,
	NonPlanar,	
	NoReport,
	NotConnectedError,
	*NR,
	NR_TOC,
	NumBdryComps,
	NumComps,
	NumCuttingDiskSurgeryRel,	
	NumDelRelators,	
	NumEdges,
	NumEmptyRels,
	NumExp_Sur_Rel,	
	NumFaces,
	NumGenerators,	
	NumKnot_Or_Link_Rel,
	*NumLoops,	
	NumRelators,
	NumSepComps,
	NumTimes,
	OnlyReducingBandsums,
	*PRIM,
	RandomizeSlides,
	ReadPres,	
	*SaveBdry,
	Save_Init_Pres,
	SaveMinima,
	Saved_Vertices,
	SepPairs,
	**SFSols,
	SFSolV[20],
	SMicro_Print,
	SRError,
	SReadPres,
	SSSReadPres,
	*SURNumX,
	*Table1,	
	TotalComp,
	UserSaidQuit,
	Vertices,
	WhichInput,
	*X,
	*Y;	
							 
extern unsigned int
	*A[VERTICES],
	*AA[VERTICES],
	*AJ1[VERTICES],
	*AJ2[VERTICES],
	*AJ3[VERTICES],
	*AT,
	*B[VERTICES],
	*Bdry,
	*BeenChecked,
	BNumNotConnected,
	BNumNotRealizable,
	*BSV1,
	*BSV2,
	*ComponentNum,
	CouldNotRemove,
	*Daughters,
	*DF,
	*DRA[2*MAXNUMRELATORS],
	Dup_On_File,
	*ED[(VERTICES)/2],
	*EXL[(VERTICES)/2],
	*EXP[(VERTICES)/2],
	*EXR[(VERTICES)/2],
	*Father,
	*FR,
	From_BANDSUM,
	From_DUALIZE,
	*GV2,
	*GV2L,
	*GV2R,
	*HegSplNum,
	*HegSplNxt,
	*InQueue,
	*IV,
	LastPresRead,
	*Left,
	LensSpace,	
	*Lowpt,
	MaxLength,
	Mergers,
	MyMaxSavedPres,
	MyMaxSavedPres3,
	MyMaxSavedPres4,
	*NEBC,	
	*NEX[(VERTICES)/2],
	*NFBC,	
	NotNewPres,
	*NRBC,	
	*Number,
	NumFilled,
	NumRealizable,
	NumRelTooLong,
	Num_Saved_LPres,
	*Num_Sep_Vertex_Pairs,
	NumNonSepAnnuli,
	NumNotConnected,
	NumPresExamined,
	NumSepAnnuli,
	NumSymmetries,
	NumVert,
	OnStack,
	*OSA,
	*OSB,
	*PG,
	*Right,
	Start_Level_Search,
	Starting_Pres,
	Stopper,
	*SUR_Num,
	*SV,
	This_Pres,
	*TV,
	*UDV,
	*UnUsed_Sep_Vertex_Pairs,
	*UpDate,
	*V,
	*VA,
	*VWG,
	V1,
	V2,
	Word1,
	Word2,
	*XX,
	*YY, 	
	*ZZ,
	*zz;

extern long
	Band_Sums,
	MaxTotalLength,
	Minimum,
	MyMaxNumDiagrams,
	MyMaxNumDiagrams3,
	NumDiagrams,
	Recip_P,
	Recip_Q;

extern unsigned long 	
	Automorphisms,
	BytesAvailable,
	BytesUsed,
	*HegSplNumMinL,
	HS_Rep_Length,	
	Length,
	Length1,
	Length2,
	*LR,
	*LSP,
	*LSQ,
	MinLength,	
	*MLC[MAXNUMCOMPONENTS],	
	NumDualized,
	NumErrors,
	Num_Level_Slides,
	Num_Level_Transformations,
	OrigLength,
	P,
	Q,
	SLength,
	SNumErrors,
	SNum_Level_Slides,
	*SURL,
	TOCLength,
	TotalAuts;
		