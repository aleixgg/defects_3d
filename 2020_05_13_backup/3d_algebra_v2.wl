(* ::Package:: *)

(* ::Input:: *)
(*Quit*)


(* ::Section:: *)
(*Libraries*)


(* ::Subsection::Closed:: *)
(*Commutation / Anti-Commutation*)


ClearAll[Grading,Fermion,Boson]
Grading[a_Plus]:=Max@@(Grading/@(List@@a));
Grading[a_Times|a_CenterDot]:=Plus @@ (Grading /@ (List @@ a));
Grading[a_^b_]:=b Grading[a];
Grading[_]:=0;
Fermion[a__]:=(Grading[#]=1)&/@{a}; 
Boson[a__]:=(Grading[#]=2)&/@{a};

ClearAll[GetOrder,SetOrder,InternalOrderedQ]
GetOrder[_]:=0
SetOrder[a_,order_Integer]:=(GetOrder[a]=order);
SetOrder[a_List,order_Integer]:=(GetOrder[#]=order)&/@a;
InternalOrderedQ[a_,b_]:=Module[
	{oa=GetOrder[a],ob=GetOrder[b]},
	If[oa==ob,OrderedQ[{a,b}],oa<ob]
]
ClearAll[Commutator,AntiCommutator,GradedCommutator,SetCommutator,SetAntiCommutator,GradedComm,ClearGradedComm]
Commutator[a_,b_]:=a\[CenterDot]b-b\[CenterDot]a;
AntiCommutator[a_,b_]:=a\[CenterDot]b+b\[CenterDot]a;
GradedCommutator[a_,b_]:=a\[CenterDot]b-(-1)^(Grading[a]Grading[b]) b\[CenterDot]a;
SetCommutator[a_, b_, com_]/;And[Grading[a]!=0,Grading[b]!=0] := Module[{},
	GradedComm[a, b]=com;
	GradedComm[b, a]=(-1)^(Grading[a]Grading[b]+1) com;
];
SetAntiCommutator=SetCommutator;
GradedComm[___]:=0
ClearGradedComm:=(ClearAll[GradedComm];GradedComm[___]:=0);

ClearAll[CenterDot]
CenterDot[a___,b_Plus,c___]:=CenterDot[a,#,c]&/@b
CenterDot[a___,b_ d_,c___]:=CenterDot[a,b,d,c]
CenterDot[a___,b_,c___]/;Grading[b]==0:=b CenterDot[a,c]
CenterDot[a___,b_,c_,d___]/;!InternalOrderedQ[b,c]&&Grading[b]!=0&&Grading[c]!=0:=(-1)^(Grading[b]Grading[c])CenterDot[a,c,b,d]+CenterDot[a,GradedComm[b,c],d]
CenterDot[a___,b_,b_,d___]/;Grading[b]==1:=1/2CenterDot[a,GradedComm[b,b],d]
CenterDot[a___, 0, b___] := 0
CenterDot[a_]:=a
CenterDot[]:=1
SetAttributes[CenterDot,Flat]

(* Function to collect center dot *)
CollectCD[expr_,fun_:Identity]:=Collect[expr,HoldPattern[CenterDot[___]],fun]


(* ::Subsection::Closed:: *)
(*Fermionic derivatives*)


Clear[SetNumeric,NumQ]
SetNumeric[a__]:=(NumQ[#]=True)&/@{a};
NumQ[x_]:=NumericQ[x];

Clear[der]
der[a_Plus,x__]:=der[#,x]&/@a
der[a_ b_,x__]:=(-1)^(Grading[b]Grading[x]) b\[CenterDot]der[a,x]+(-1)^(Grading[a]Grading[x]) a\[CenterDot]der[b,x]
der[a_^b_,x__]:=b a^(b-1) der[a,x]
der[num_?NumQ,x__]:=0
der[HoldPattern[a_\[CenterDot]b_],x__]:=der[a,x]\[CenterDot]b+(-1)^(Grading[a]Grading[x]) a\[CenterDot]der[b,x]
der[der[f_,A_],B_]/;Not@InternalOrderedQ[A,B]:=(-1)^(Grading[A]Grading[B])der[der[f,B],A];
der[der[f_,A_],A_]/;OddQ@Grading[A]:=0;
Grading[der[a_,b_]]:=Grading[a]+Grading[b];


(* ::Section::Closed:: *)
(*Conventions*)


Clear[\[Delta], \[CapitalSigma], \[CapitalSigma]b, m, mb]
\[Delta] = KroneckerDelta;
\[CapitalSigma][0][\[Alpha]_, \[Alpha]d_]   := PauliMatrix[1][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][1][\[Alpha]_, \[Alpha]d_]   := PauliMatrix[2][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][2][\[Alpha]_, \[Alpha]d_]   := PauliMatrix[3][[\[Alpha], \[Alpha]d]];
\[CapitalSigma]b[\[Mu]_][\[Alpha]d_, \[Alpha]_] := Conjugate[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d]];
m[\[Mu]_, \[Nu]_][\[Alpha]_, \[Beta]_] := m[\[Mu], \[Nu]][\[Alpha], \[Beta]] = -I/4 Sum[
	\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]] -
	\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]]
, {\[Alpha]d, 2}];
mb[\[Mu]_, \[Nu]_][\[Alpha]d_, \[Beta]d_] := mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] = -I/4 Sum[
	\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d] -
	\[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Mu]][\[Alpha], \[Beta]d]
, {\[Alpha], 2}];


(* ::Subsection:: *)
(*Checks *)


(* ::Text:: *)
(*Eq. (9)*)


Table[
	Sum[\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]], {\[Alpha]d, 2}] == 
	\[Delta][\[Alpha], \[Beta]] \[Delta][\[Mu], \[Nu]] + 2 I m[\[Mu], \[Nu]][\[Alpha], \[Beta]]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates
Table[
	Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d], {\[Alpha], 2}] == 
	\[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Mu], \[Nu]] + 2 I mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha]d, 2}, {\[Beta]d, 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (10)*)


Table[{
	Sum[
		\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]] + 
		\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]]
	, {\[Alpha]d, 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha], \[Beta]],
	Sum[
		\[CapitalSigma]b[\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma][\[Nu]][\[Alpha]d, \[Beta]] + 
		\[CapitalSigma]b[\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma][\[Mu]][\[Alpha]d, \[Beta]]
	, {\[Alpha]d, 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha], \[Beta]]
}, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (14)*)


Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Mu], 0, 2}] == 2 3


(* ::Section:: *)
(*Bulk Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations*)


Boson[\[ScriptCapitalD], \[ScriptCapitalP][_], \[ScriptCapitalK][_], \[ScriptCapitalM][_, _], \[ScriptCapitalR]];
Fermion[\[ScriptCapitalQ]p[_], \[ScriptCapitalQ]m[_], \[ScriptCapitalS]p[_], \[ScriptCapitalS]m[_]];

\[ScriptCapitalM][\[Mu]_, \[Nu]_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM][\[Nu], \[Mu]];
\[ScriptCapitalM][\[Mu]_, \[Mu]_] := 0;

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]], -I \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]], +I \[ScriptCapitalK][\[Mu]]], {\[Mu], 0, 2}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Nu]], 2I (\[Delta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]])], {\[Mu], 0, 2}, {\[Nu], 0, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalM][\[Rho], \[Sigma]], I(
	+ \[Delta][\[Mu], \[Rho]] \[ScriptCapitalM][\[Nu], \[Sigma]]
	- \[Delta][\[Nu], \[Rho]] \[ScriptCapitalM][\[Mu], \[Sigma]]
	- \[Delta][\[Mu], \[Sigma]] \[ScriptCapitalM][\[Nu], \[Rho]]
	+ \[Delta][\[Nu], \[Sigma]] \[ScriptCapitalM][\[Mu], \[Rho]]
)], {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}, {\[Sigma], 0, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]], I (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]], I (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}];

Table[SetAntiCommutator[\[ScriptCapitalQ]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[\[CapitalSigma][\[Mu]][\[Alpha],\[Alpha]d] \[ScriptCapitalP][\[Mu]], {\[Mu], 0, 2}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalS]m[\[Alpha]], Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalK][\[Mu]], {\[Mu], 0, 2}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 
	+ \[Delta][\[Alpha], \[Beta]] (I \[ScriptCapitalD] - \[ScriptCapitalR]) 
	+ Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]]
, {\[Alpha], 2}, {\[Beta], 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalQ]m[\[Beta]d], 
	+ \[Delta][\[Alpha]d, \[Beta]d] (I \[ScriptCapitalD] + \[ScriptCapitalR]) 
	+ Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]]
, {\[Alpha]d, 2}, {\[Beta]d, 2}];

Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]p[\[Alpha]],  + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], 0, 2}, {\[Alpha],  2}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]m[\[Alpha]d], + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]m[\[Alpha]] , {\[Alpha],  2}]], {\[Mu], 0, 2}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]p[\[Alpha]d], - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]p[\[Alpha]],  {\[Alpha],  2}]], {\[Mu], 0, 2}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]m[\[Alpha]],  - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]m[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], 0, 2}, {\[Alpha] , 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]p[\[Alpha]], Sum[m[\[Mu], \[Nu]][\[Alpha], \[Beta]] \[ScriptCapitalQ]p[\[Beta]], {\[Beta], 2}]]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d] \[ScriptCapitalQ]m[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]p[\[Alpha]d], -Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalS]p[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]m[\[Alpha]], -Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalS]m[\[Beta]], {\[Beta], 2}]]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Alpha], 2}];

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalQ]p[\[Alpha]],  -I/2 \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalQ]m[\[Alpha]d], -I/2 \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalS]p[\[Alpha]d], +I/2 \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalS]m[\[Alpha]],  +I/2 \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}];

Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalQ]p[\[Alpha]],  + \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalQ]m[\[Alpha]d], - \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalS]p[\[Alpha]d], + \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalS]m[\[Alpha]],  - \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}];


(* ::Subsection::Closed:: *)
(*Check Jacobi identities*)


allOperators = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalR]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, 2}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}],
	Table[{\[ScriptCapitalQ]p[\[Alpha]], \[ScriptCapitalS]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalS]m[\[Alpha]]}, {\[Alpha], 2}]
];
allCombinations = Flatten[Outer[List, allOperators, allOperators, allOperators], 2];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
evalJacobiIdentity[X_, Y_, Z_] := ( 
	+ (-1)^(Grading[X] Grading[Z]) GradedCommutator[GradedCommutator[X, Y], Z]
	+ (-1)^(Grading[Z] Grading[Y]) GradedCommutator[GradedCommutator[Z, X], Y]
	+ (-1)^(Grading[Y] Grading[X]) GradedCommutator[GradedCommutator[Y, Z], X]
);
jacId = evalJacobiIdentity @@@ allCombinations // Simplify // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Casimir*)


\[ScriptCapitalC]2=( 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[\[ScriptCapitalP][\[Mu]]\[CenterDot]\[ScriptCapitalK][\[Mu]] + \[ScriptCapitalK][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]], {\[Mu], 0, 2}]
	+ 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
	- 1/2 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 Sum[\[ScriptCapitalS]p[\[Alpha]d]\[CenterDot]\[ScriptCapitalQ]m[\[Alpha]d] - \[ScriptCapitalQ]m[\[Alpha]d]\[CenterDot]\[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]
	+ 1/2 Sum[\[ScriptCapitalS]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]] - \[ScriptCapitalQ]p[\[Alpha]]\[CenterDot]\[ScriptCapitalS]m[\[Alpha]], {\[Alpha], 2}]
);
Table[Commutator[\[ScriptCapitalC]2, op], {op, allOperators}] // Expand // Flatten // DeleteDuplicates


(* ::Section:: *)
(*Defect Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations \[ScriptCapitalN]=1*)


(* ::Text:: *)
(*Commutation relations*)


Clear[\[ScriptCapitalL], \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
Boson[\[ScriptCapitalL][_]];
Fermion[\[ScriptCapitalG][_]];

Table[SetCommutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n], (m-n) \[ScriptCapitalL][m+n]], {m, -1, 1}, {n, -1, 1}];
Table[SetCommutator[\[ScriptCapitalL][m], \[ScriptCapitalG][r], (m/2 - r) \[ScriptCapitalG][m+r]], {m, -1, 1}, {r, -1/2, 1/2}];
Table[SetAntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG][s], 2 \[ScriptCapitalL][r+s]], {r, -1/2, 1/2}, {s, -1/2, 1/2}];


(* ::Text:: *)
(*Check Jacobi identities*)


allOperators = Flatten @ Join[
	Table[\[ScriptCapitalL][m], {m, -1, 1}],
	Table[\[ScriptCapitalG][r], {r, -1/2, 1/2}]
];
allCombinations = Flatten[Outer[List, allOperators, allOperators, allOperators], 2];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
evalJacobiIdentity[X_, Y_, Z_] := ( 
	+ (-1)^(Grading[X] Grading[Z]) GradedCommutator[GradedCommutator[X, Y], Z]
	+ (-1)^(Grading[Z] Grading[Y]) GradedCommutator[GradedCommutator[Z, X], Y]
	+ (-1)^(Grading[Y] Grading[X]) GradedCommutator[GradedCommutator[Y, Z], X]
);
jacId = evalJacobiIdentity @@@ allCombinations // Simplify // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Commutation relations \[ScriptCapitalN]=2*)


(* ::Text:: *)
(*Commutation relations*)


Clear[\[ScriptCapitalL], \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
Boson[\[ScriptCapitalL][_], \[ScriptCapitalJ][_]];
Fermion[\[ScriptCapitalG][_], \[ScriptCapitalG]b[_]];

Table[SetCommutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n], (m-n) \[ScriptCapitalL][m+n]], {m, -1, 1}, {n, -1, 1}];
Table[SetCommutator[\[ScriptCapitalL][m], \[ScriptCapitalG][r],  (m/2 - r) \[ScriptCapitalG][m+r]],  {m, -1, 1}, {r, -1/2, 1/2}];
Table[SetCommutator[\[ScriptCapitalL][m], \[ScriptCapitalG]b[r], (m/2 - r) \[ScriptCapitalG]b[m+r]], {m, -1, 1}, {r, -1/2, 1/2}];
Table[SetCommutator[\[ScriptCapitalJ][m], \[ScriptCapitalG][r],  +\[ScriptCapitalG][m+r]],  {m, 0, 0}, {r, -1/2, 1/2}];
Table[SetCommutator[\[ScriptCapitalJ][m], \[ScriptCapitalG]b[r], -\[ScriptCapitalG]b[m+r]], {m, 0, 0}, {r, -1/2, 1/2}];
Table[SetAntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG]b[s], \[ScriptCapitalL][r+s] + 1/2(r-s) \[ScriptCapitalJ][r+s]], {r, -1/2, 1/2}, {s, -1/2, 1/2}];


(* ::Text:: *)
(*Check Jacobi identities*)


allOperators = Flatten @ Join[
	{\[ScriptCapitalJ][0]}, 
	Table[\[ScriptCapitalL][m], {m, -1, 1}],
	Table[{\[ScriptCapitalG][r], \[ScriptCapitalG]b[r]}, {r, -1/2, 1/2}]
];
allCombinations = Flatten[Outer[List, allOperators, allOperators, allOperators], 2];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
evalJacobiIdentity[X_, Y_, Z_] := ( 
	+ (-1)^(Grading[X] Grading[Z]) GradedCommutator[GradedCommutator[X, Y], Z]
	+ (-1)^(Grading[Z] Grading[Y]) GradedCommutator[GradedCommutator[Z, X], Y]
	+ (-1)^(Grading[Y] Grading[X]) GradedCommutator[GradedCommutator[Y, Z], X]
);
jacId = evalJacobiIdentity @@@ allCombinations // Simplify // DeleteDuplicates


(* ::Subsection:: *)
(*Embedding of (2,0) subalgebra*)


(* ::Text:: *)
(*Check that the subalgebra closes and satisfies Jacobi:*)


allDefOps = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalR]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, 1}],
	{\[ScriptCapitalM][0, 1]},
	{\[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1], \[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]}
];
defOpsToZero = # -> 0 & /@ allDefOps;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-I \[ScriptCapitalD] + \[ScriptCapitalM][0, 1]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][0] - I \[ScriptCapitalP][1]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][0] + I \[ScriptCapitalK][1]);
\[ScriptCapitalL]b[0]  = 1/2 (-I \[ScriptCapitalD] - \[ScriptCapitalM][0, 1]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][0] + I \[ScriptCapitalP][1]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][0] - I \[ScriptCapitalK][1]);
\[ScriptCapitalJ][0] = \[ScriptCapitalR];
\[ScriptCapitalG][+1/2]  = - \[ScriptCapitalQ]p[1] / Sqrt[2];
\[ScriptCapitalG][-1/2]  = + \[ScriptCapitalS]p[2] / Sqrt[2];
\[ScriptCapitalG]b[+1/2] = - \[ScriptCapitalQ]m[2] / Sqrt[2];
\[ScriptCapitalG]b[-1/2] = + \[ScriptCapitalS]m[1] / Sqrt[2];
scharges = {\[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1], \[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]};
\[ScriptCapitalG][r_]  := Sum[c[r, i]  scharges[[i]], {i, 4}];
\[ScriptCapitalG]b[r_] := Sum[cb[r, i] scharges[[i]], {i, 4}];
eqs = Join[{
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n]]  - (m-n) \[ScriptCapitalL][m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalL]b[n]] - (m-n) \[ScriptCapitalL]b[m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL]b[n]], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalG][r]]  - (m/2 - r) \[ScriptCapitalG][m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalG]b[r]] - (m/2 - r) \[ScriptCapitalG]b[m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG][r]]  - \[ScriptCapitalG][m+r],  {m, 0, 0}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG]b[r]] + \[ScriptCapitalG]b[m+r], {m, 0, 0}, {r, -1/2, 1/2}],
	Table[AntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG]b[s]] - (\[ScriptCapitalL][r+s] + 1/2(r-s) \[ScriptCapitalJ][r+s]) , {r, -1/2, 1/2}, {s, -1/2, 1/2}]
}] // Expand // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2def = ( 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 1}]
	+ \[ScriptCapitalM][0, 1]\[CenterDot]\[ScriptCapitalM][0, 1]
	- 1/2 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 Commutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates


(* ::Text:: *)
(*Casimir eigenvalue*)


Expand[ 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 1}]
	+ \[ScriptCapitalM][0, 1]\[CenterDot]\[ScriptCapitalM][0, 1]
	- 1/2 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> -I \[CapitalDelta],
	\[ScriptCapitalM][0, 1] -> l,
	\[ScriptCapitalR] -> r
} // Simplify


(* ::Subsection:: *)
(*Embedding of (1,1) subalgebra*)


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-I \[ScriptCapitalD] + \[ScriptCapitalM][0, 1]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][0] - I \[ScriptCapitalP][1]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][0] + I \[ScriptCapitalK][1]);
\[ScriptCapitalG][+1/2] = +1 / Sqrt[2] (\[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1]);
\[ScriptCapitalG][-1/2] = -1 / Sqrt[2] (\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2]);
\[ScriptCapitalL]b[0]  = 1/2 (-I \[ScriptCapitalD] - \[ScriptCapitalM][0, 1]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][0] + I \[ScriptCapitalP][1]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][0] - I \[ScriptCapitalK][1]);
\[ScriptCapitalG]b[+1/2] = +1 / Sqrt[2] (\[ScriptCapitalQ]p[2] + \[ScriptCapitalQ]m[1]);
\[ScriptCapitalG]b[-1/2] = -1 / Sqrt[2] (\[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2]);


Join[
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n]]  - (m-n) \[ScriptCapitalL][m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalG][r]]  - (m/2 - r) \[ScriptCapitalG][m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[AntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG][s]] - 2 \[ScriptCapitalL][r+s], {r, -1/2, 1/2}, {s, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalL]b[n]]  - (m-n) \[ScriptCapitalL]b[m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalG]b[r]]  - (m/2 - r) \[ScriptCapitalG]b[m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[AntiCommutator[\[ScriptCapitalG]b[r], \[ScriptCapitalG]b[s]] - 2 \[ScriptCapitalL]b[r+s], {r, -1/2, 1/2}, {s, -1/2, 1/2}]
] // Expand // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


allDefOps = Flatten @ Join[
	Table[{\[ScriptCapitalL][m], \[ScriptCapitalL]b[m]}, {m, -1, 1}],
	Table[{\[ScriptCapitalG][r], \[ScriptCapitalG]b[r]}, {r, -1/2, 1/2}]
];
\[ScriptCapitalC]2def = ( 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalK][\[Mu]]], {\[Mu], 0, 1}]
	+ \[ScriptCapitalM][0, 1]\[CenterDot]\[ScriptCapitalM][0, 1]
	+ 1/4 Commutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1]]
	+ 1/4 Commutator[\[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] + \[ScriptCapitalQ]m[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates


Expand[
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 1}]
	+ \[ScriptCapitalM][0, 1]\[CenterDot]\[ScriptCapitalM][0, 1] 
	+ 1/4 AntiCommutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1]]
	+ 1/4 AntiCommutator[\[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] + \[ScriptCapitalQ]m[1]]
] /. {
	\[ScriptCapitalD] -> -I \[CapitalDelta],
	\[ScriptCapitalM][0, 1] -> l
} // Simplify


(* ::Subsection:: *)
(*Calculate blocks*)


(* ::Text:: *)
(*Action using differential operators*)


IxP = I Sum[x[\[Mu]] \[ScriptCapitalP][\[Mu]], {\[Mu], 0, 2}];
expSer = 1 + IxP + IxP\[CenterDot]IxP/2 + IxP\[CenterDot]IxP\[CenterDot]IxP/6 // Expand;
truncate = HoldPattern@CenterDot[_, _, _, _] :> 0;
Table[
	lhs = \[ScriptCapitalP][\[Mu]]\[CenterDot]expSer; 
	rhs = -I D[expSer, x[\[Mu]]];
	lhs - rhs
, {\[Mu], 0, 2}] /. truncate //Expand // Flatten // DeleteDuplicates
Table[
	lhs = Commutator[\[ScriptCapitalM][\[Mu], \[Nu]], expSer];
	rhs = +I (x[\[Mu]] D[expSer, x[\[Nu]]] - x[\[Nu]] D[expSer, x[\[Mu]]]);
	lhs - rhs
, {\[Mu], 0, 2}, {\[Nu], 0, 2}] /. truncate //Expand // Flatten // DeleteDuplicates


Sum[(  
	+ 1/2 Commutator[\[ScriptCapitalS]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Alpha]]]
) - (
	- \[ScriptCapitalQ]m[\[Alpha]]\[CenterDot]\[ScriptCapitalS]p[\[Alpha]] 
	+ \[ScriptCapitalS]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]]
), {\[Alpha], 2}] // Expand


expr = (
	+ AntiCommutator[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] 
	- term[1, 1]
) /. {
	\[ScriptCapitalP][\[Mu]_] :> -I d[1][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[1][\[Mu]] d[1][\[Nu]] - x[1][\[Nu]] d[1][\[Mu]])
}
rule11 = Solve[% == 0, term[1, 1]][[1, 1]]


expr = (
	+ AntiCommutator[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] 
	- term[2, 1]
) /. {
	\[ScriptCapitalP][\[Mu]_] :> -I d[1][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[1][\[Mu]] d[1][\[Nu]] - x[1][\[Nu]] d[1][\[Mu]])
}
rule21 = Solve[% == 0, term[2, 1]][[1, 1]]


expr = (
	+ AntiCommutator[\[ScriptCapitalQ]m[2], \[ScriptCapitalQ]p[2]] 
	+ term[2, 2]
) /. {
	\[ScriptCapitalP][\[Mu]_] :> -I d[2][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[2][\[Mu]] d[2][\[Nu]] - x[2][\[Nu]] d[2][\[Mu]])
}
rule22 = Solve[% == 0, term[2, 2]][[1, 1]]


expr = (
	+ AntiCommutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[1]] 
	- I Sum[x[2][\[Mu]] \[CapitalSigma]b[\[Mu]][2, \[Alpha]] term[1, \[Alpha]],  {\[Mu], 0, 2}, {\[Alpha], 2}]
) /. {
	\[ScriptCapitalP][\[Mu]_] :> -I d[1][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[1][\[Mu]] d[1][\[Nu]] - x[1][\[Nu]] d[1][\[Mu]]),
	term[1,1] -> -I d[1][2]
}
rule12 = Solve[% == 0, term[1, 2]][[1, 1]] // Simplify


expr = (
	+ I Sum[x[1][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, 1] term[\[Alpha]d, 1], {\[Mu], 0, 2}, {\[Alpha]d, 2}]
	+ AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]] 
) /. {
	\[ScriptCapitalP][\[Mu]_] :> -I d[2][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[2][\[Mu]] d[2][\[Nu]] - x[2][\[Nu]] d[2][\[Mu]]),
	term[2, 2] -> -I d[2][2]
}
rule21 = Solve[% == 0, term[2,1]][[1, 1]] // Simplify


((-I d[1][0]+d[1][1]) x[1][2]+d[1][2] (I x[1][0]-x[1][1]-I x[2][0]+x[2][1]))/x[2][2] - (
	1 / x[2][2] (
		+ (I (x[1][0] - x[2][0]) - (x[1][1] - x[2][1])) d[1][2]
		- x[1][2] (I d[1][0] - d[1][1])
	)
) // ExpandAll


(d[2][2] (I x[1][0]-x[1][1]-I x[2][0]+x[2][1])+I (d[2][0]+I d[2][1]) x[2][2])/x[1][2] - (
	1 / x[1][2] (
		+ (I (x[1][0] - x[2][0]) - (x[1][1] - x[2][1])) d[2][2]
		+ x[2][2] (I d[2][0] - d[2][1])
	)
)// ExpandAll


(* ::Subsection:: *)
(*Ward Identities*)


\[ScriptCapitalS]p[2] + Sum[x[\[Mu]] \[CapitalSigma]b[\[Mu]][2, \[Alpha]]  \[ScriptCapitalQ]p[\[Alpha]],  {\[Mu], 0, 1}, {\[Alpha],  2}]
\[ScriptCapitalS]m[1] + Sum[x[\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, 1] \[ScriptCapitalQ]m[\[Alpha]d], {\[Mu], 0, 1}, {\[Alpha]d, 2}]


1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]] + 1/2 Commutator[\[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2]] + \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2]\[CenterDot]\[ScriptCapitalQ]p[2] // Expand


Sum[(  
	+ 1/2 Commutator[\[ScriptCapitalS]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Alpha]]]
) - (
	- \[ScriptCapitalQ]m[\[Alpha]]\[CenterDot]\[ScriptCapitalS]p[\[Alpha]] 
	+ \[ScriptCapitalS]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]]
), {\[Alpha], 2}] // Expand


+ I Sum[(x[1][\[Mu]]-x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term[\[Alpha]d, \[Alpha]], {\[Mu], 0, 2}, {\[Alpha], 2}, {\[Alpha]d, 2}] /. {
	term[1, 2] -> (d[2][2] (I x[1][0]-x[1][1]-I x[2][0]+x[2][1])+I (d[2][0]+I d[2][1]) x[2][2])/x[1][2],
	term[2, 2] -> -I d[2][2],
	term[1, 1] -> -I d[1][2],
	term[2, 1] -> -I d[1][0] - d[1][1]
} // Expand


+ I Sum[x[1][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term[\[Alpha]d, \[Alpha]], {\[Mu], 0, 2}, {\[Alpha],  2}, {\[Alpha]d, 2}] // Expand
- I Sum[x[2][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term[\[Alpha]d, \[Alpha]],  {\[Mu], 0, 2}, {\[Alpha],  2}] // Expand
terms = % + %% // Collect[#, term[__], Factor] &


(terms /. {
	term[1, 2] -> (d[2][2] (I x[1][0]-x[1][1]-I x[2][0]+x[2][1])+I (d[2][0]+I d[2][1]) x[2][2])/x[1][2],
	term[2, 2] -> -I d[2][2],
	term[1, 1] -> -I d[1][2],
	term[2, 1] -> -I d[1][0] - d[1][1]
}) - (
	- x[1][2] d[2][2]
	- x[2][2] d[1][2]
	- ((x[1][0]-x[2][0])^2 + (x[1][1]-x[2][1])^2) / x[1][2] d[2][2]
	- ((x[1][0]-x[2][0]) d[2][0] + (x[1][1]-x[2][1]) d[2][1]) x[2][2] / x[1][2]
	- I ((x[1][0]-x[2][0]) d[2][1] - (x[1][1]-x[2][1]) d[2][0]) x[2][2] / x[1][2]
) // ExpandAll


(* ::Section::Closed:: *)
(*Differential operators*)


(* ::Subsection:: *)
(*Definitions*)


\[ScriptCapitalD]d[i_][expr_] := -I ( Sum[x[i][\[Mu]] der[expr, x[i][\[Mu]]], {\[Mu], 0, 2}] + \[CapitalDelta][i] expr );
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := -I der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := -I (
	+ Sum[\[Eta][\[Nu], \[Nu]] x[i][\[Nu]]^2, {\[Nu], 0, 2}] der[expr, x[i][\[Mu]]]
	- 2 \[Eta][\[Mu], \[Mu]] x[i][\[Mu]] Sum[x[i][\[Nu]] der[expr, x[i][\[Nu]]], {\[Nu], 0, 2}]
	- 2 \[Eta][\[Mu], \[Mu]] x[i][\[Mu]] \[CapitalDelta][i] expr
);
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -I (
	+ \[Eta][\[Mu], \[Mu]] x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- \[Eta][\[Nu], \[Nu]] x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);


multiPointOp[op_] := (
	op[i___][expr_] := Total[op[#][expr]& /@ {i}]
);
multiPointOp[\[ScriptCapitalD]d];
Table[multiPointOp[\[ScriptCapitalP]d[\[Mu]]], {\[Mu], 0, 2}];
Table[multiPointOp[\[ScriptCapitalK]d[\[Mu]]], {\[Mu], 0, 2}];
Table[multiPointOp[\[ScriptCapitalM]d[\[Mu], \[Nu]]], {\[Mu], 0, 2}, {\[Nu], 0, 2}];


(* ::Subsection::Closed:: *)
(*Check commutation relations*)


dummyFun = f[x[1][0], x[1][1], x[1][2]];
ruleRhs = {
	\[ScriptCapitalD]d :> \[ScriptCapitalD]d[1][dummyFun],
	\[ScriptCapitalP]d[\[Mu]_] :> \[ScriptCapitalP]d[\[Mu]][1][dummyFun],
	\[ScriptCapitalK]d[\[Mu]_] :> \[ScriptCapitalK]d[\[Mu]][1][dummyFun],
	\[ScriptCapitalM]d[\[Mu]_, \[Nu]_] :> \[ScriptCapitalM]d[\[Mu], \[Nu]][1][dummyFun]
};
CheckCommutator[op1_, op2_, expr_] := (
	+ op1[1][op2[1][dummyFun]]
	- op2[1][op1[1][dummyFun]]
	- (expr /. ruleRhs)
);


der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Delta][\[Mu], \[Nu]]
SetNumeric[\[CapitalDelta][_]];
Table[CheckCommutator[\[ScriptCapitalD]d, \[ScriptCapitalP]d[\[Mu]], +I \[ScriptCapitalP]d[\[Mu]]], {\[Mu], 0, 2}] // Expand // Flatten // DeleteDuplicates
Table[CheckCommutator[\[ScriptCapitalD]d, \[ScriptCapitalK]d[\[Mu]], -I \[ScriptCapitalK]d[\[Mu]]], {\[Mu], 0, 2}] // Expand // Flatten // DeleteDuplicates
Table[CheckCommutator[\[ScriptCapitalP]d[\[Mu]], \[ScriptCapitalK]d[\[Nu]], 2I (\[Eta][\[Mu],\[Nu]] \[ScriptCapitalD]d - \[ScriptCapitalM]d[\[Mu], \[Nu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}] // Expand // Flatten // DeleteDuplicates
Table[CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalM]d[\[Rho], \[Sigma]], I(
	+ \[Eta][\[Mu], \[Rho]] \[ScriptCapitalM]d[\[Nu], \[Sigma]]
	- \[Eta][\[Nu], \[Rho]] \[ScriptCapitalM]d[\[Mu], \[Sigma]]
	- \[Eta][\[Mu], \[Sigma]] \[ScriptCapitalM]d[\[Nu], \[Rho]]
	+ \[Eta][\[Nu], \[Sigma]] \[ScriptCapitalM]d[\[Mu], \[Rho]]
)], {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}, {\[Sigma], 0, 2}] // Expand // Flatten // DeleteDuplicates
Table[CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalP]d[\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalP]d[\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalP]d[\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}] // Expand // Flatten // DeleteDuplicates
Table[CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalK]d[\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalK]d[\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalK]d[\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}] // Expand // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Casimir*)


\[ScriptCapitalC]2d[i__][expr_] := ( 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]](\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]]), {\[Mu], 0, 2}]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]] \[Eta][\[Nu], \[Nu]] \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Nu], \[Mu]][i]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
);


(* ::Section::Closed:: *)
(*Bulk Correlation functions*)


(* ::Subsection::Closed:: *)
(*Definitions*)


Clear[x2, x2Val]
der[x2[i_, j_], x[k_][\[Mu]_]] := 2 \[Eta][\[Mu], \[Mu]] (x[i][\[Mu]]-x[j][\[Mu]]) (\[Delta][i, k] - \[Delta][j, k])
x2Val[i_, j_] := Sum[\[Eta][\[Mu], \[Mu]] (x[i][\[Mu]] - x[j][\[Mu]])^2, {\[Mu], 0, 2}];


checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][i__][expr_] := Join[
	{\[ScriptCapitalD]d[i][expr]},
	Table[\[ScriptCapitalP]d[\[Mu]][i][expr], {\[Mu], 0, 2}],
	Table[\[ScriptCapitalK]d[\[Mu]][i][expr], {\[Mu], 0, 2}],
	Table[\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
]


randRule = Flatten[{
	Table[x[i][\[Mu]] -> RandomReal[], {i, 4}, {\[Mu], 0, 2}],
	Table[\[CapitalDelta][i] -> RandomReal[], {i, 4}]
}];


(* ::Subsection::Closed:: *)
(*Two-point function*)


twoPtFun = x2[1, 2]^(-\[CapitalDelta][1]);
expr = x2[1, 2]^(\[CapitalDelta][1]+1) checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2][twoPtFun] /. {\[CapitalDelta][2] -> \[CapitalDelta][1], x2 -> x2Val};
expr // Together // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Three-point function*)


threePtFun = (
	x2[1, 2]^((-\[CapitalDelta][1]-\[CapitalDelta][2]+\[CapitalDelta][3]) / 2)
	x2[1, 3]^((-\[CapitalDelta][1]-\[CapitalDelta][3]+\[CapitalDelta][2]) / 2)
	x2[3, 2]^((-\[CapitalDelta][3]-\[CapitalDelta][2]+\[CapitalDelta][1]) / 2)
);
expr = Expand[threePtFun^(-1) checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2, 3][threePtFun]] /. x2 -> x2Val;
expr // Together // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Four-point function*)


fourPtFun = (
	x2[1, 2]^((-\[CapitalDelta][1]-\[CapitalDelta][2]) / 2)
	x2[3, 4]^((-\[CapitalDelta][3]-\[CapitalDelta][4]) / 2)
	(x2[2, 4] / x2[1, 4])^((\[CapitalDelta][1]-\[CapitalDelta][2]) / 2)
	(x2[1, 4] / x2[1, 3])^((\[CapitalDelta][3]-\[CapitalDelta][4]) / 2)
);
expr = Expand[fourPtFun^(-1) checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2, 3, 4][fourPtFun]] /. x2 -> x2Val;
expr // Together // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Invariants*)


u = x2[1, 2] x2[3, 4] / (x2[1, 3] x2[2, 4]);
v = x2[1, 4] x2[2, 3] / (x2[1, 3] x2[2, 4]);
expr = checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2, 3, 4][u] /. \[CapitalDelta][_] -> 0;
Numerator @ Together @ expr /. x2 -> x2Val // Expand // Flatten // DeleteDuplicates
expr = checkBulk\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2, 3, 4][v] /. \[CapitalDelta][_] -> 0;
Numerator @ Together @ expr /. x2 -> x2Val // Expand // Flatten // DeleteDuplicates


(* ::Section::Closed:: *)
(*Defect Correlation functions*)


(* ::Subsection::Closed:: *)
(*Definitions*)


checkDefect\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][i__][expr_] := Join[
	{\[ScriptCapitalD]d[i][expr]},
	Table[\[ScriptCapitalP]d[\[Mu]][i][expr], {\[Mu], 0, 1}],
	Table[\[ScriptCapitalK]d[\[Mu]][i][expr], {\[Mu], 0, 1}],
	Table[\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr], {\[Mu], 0, 1}, {\[Nu], 0, 1}]
]


(* ::Subsection:: *)
(*Two-point in presence of boundary*)


(* ::Text:: *)
(*Check the invariant:*)


\[Xi]v = x2[1, 2] / (4 x[1][2] x[2][2]);
checkDefect\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2][\[Xi]v] /. \[CapitalDelta][_] -> 0 /. x2 -> x2Val // Together // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Check the correlation function:*)


twoPtFunDef = (2 x[1][2])^(-\[CapitalDelta][1]) (2 x[2][2])^(-\[CapitalDelta][2]);
expr = checkDefect\[ScriptCapitalD]\[ScriptCapitalP]\[ScriptCapitalK]\[ScriptCapitalM][1, 2][twoPtFunDef] /. x2 -> x2Val;
expr // Together // Flatten // DeleteDuplicates


(* ::Subsection:: *)
(*Compute blocks*)


Clear[\[Eta]]
der[x2[i_, j_], x[k_][\[Mu]_]] := 2 \[Eta][\[Mu], \[Mu]] (x[i][\[Mu]]-x[j][\[Mu]]) (\[Delta][i, k] - \[Delta][j, k])
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Eta][\[Mu], \[Nu]]


\[ScriptCapitalD]d[i_][expr_] := With[{\[Mu] = Unique[]}, -I ( x[i][\[Mu]] der[expr, x[i][\[Mu]]] + \[CapitalDelta][i] expr )];
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := -I der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := -I (
	+ dot[x[i], x[i]] der[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] x[i][\[Nu]] der[expr, x[i][\[Nu]]]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
);
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -I (
	+ x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


\[ScriptCapitalM]d[$30,$29][1,2][G[\[Xi]] x[1][2]^-\[CapitalDelta][1] (x2[1,2]/(x[1][2] x[2][2]))^(-(\[CapitalDelta][1]/2)-\[CapitalDelta][2]/2) x[2][2]^-\[CapitalDelta][2]]


?\[ScriptCapitalM]d


Clear[\[ScriptCapitalC]2d]
\[ScriptCapitalC]2d[i__][expr_] := With[{\[Mu] = Unique[], \[Nu] = Unique[]}, 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	+ 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	+ 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Nu], \[Mu]][i][expr]]
];


\[Xi]v = x2[1, 2] / (4 x[1][2] x[2][2]);
twoPtFunDef = (
	(2 x[1][2])^(-\[CapitalDelta][1]) 
	(2 x[2][2])^(-\[CapitalDelta][2]) 
	\[Xi]v^(-(\[CapitalDelta][1] + \[CapitalDelta][2]) / 2)
	G[\[Xi]]
);


der[G[\[Xi]], x[i_][\[Mu]_]] := G'[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];
der[G'[\[Xi]], x[i_][\[Mu]_]] := G''[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];
expr = \[ScriptCapitalC]2d[1, 2][twoPtFunDef] / twoPtFunDef // ExpandAll


expr2 = G[\[Xi]] expr / twoPtFunDef // ExpandAll


expr3 = expr2 /. x2 -> x2Val // Collect[#, f_[\[Xi]], Factor] &


xs = Flatten @ Table[x[i][\[Mu]], {i, 2}, {\[Mu], 0, 2}]


Coefficient[expr3, G[\[Xi]]]-Sum[a[i] \[Xi]v^i, {i, -3, 3}] /. x2 -> x2Val // Together // Numerator
CoefficientList[%, xs] // Flatten // DeleteDuplicates


Collect[%220,x[_][_]]


expr = %185 // Together // Numerator


expr /. x2 -> x2Val // Together // Collect[#, f_[\[Xi]], Factor] &


%187 /. x[1][0]^2->4 x[1][2] x[2][2] \[Xi]-(-x[1][1]^2-x[1][2]^2-2 x[1][0] x[2][0]+x[2][0]^2+2 x[1][1] x[2][1]-x[2][1]^2+2 x[1][2] x[2][2]-x[2][2]^2);
% // Collect[#, f_[\[Xi]], Factor] &


4 x[1][2] x[2][2](\[Xi]v /. x2 -> x2Val) == 4 x[1][2] x[2][2] \[Xi] // Expand





x[1][0]^2 /. Solve[(\[Xi]v /. x2 -> x2Val) == \[Xi], x[1][0]] // ExpandAll // FullSimplify


%187 /. x[1][0]^2


{
	x2[1,2] -> 4 \[Xi] x[1][2] x[2][2],
	x2[1,2] -> 4 \[Xi] x[1][2] x[2][2]
}
