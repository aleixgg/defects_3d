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
d = 3;
\[Delta] = KroneckerDelta;
\[CapitalSigma][0][\[Alpha]_, \[Alpha]d_] := PauliMatrix[1][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][1][\[Alpha]_, \[Alpha]d_] := PauliMatrix[2][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][2][\[Alpha]_, \[Alpha]d_] := PauliMatrix[3][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][3][\[Alpha]_, \[Alpha]d_] := I PauliMatrix[0][[\[Alpha], \[Alpha]d]];
\[CapitalSigma]b[\[Mu]_][\[Alpha]d_, \[Alpha]_] := Conjugate[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d]];
m[\[Mu]_, \[Nu]_][\[Alpha]_, \[Beta]_] := m[\[Mu], \[Nu]][\[Alpha], \[Beta]] = -I/4 Sum[
	\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]] -
	\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]]
, {\[Alpha]d, 2}];
mb[\[Mu]_, \[Nu]_][\[Alpha]d_, \[Beta]d_] := mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] = -I/4 Sum[
	\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d] -
	\[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Mu]][\[Alpha], \[Beta]d]
, {\[Alpha], 2}];


(* ::Subsection::Closed:: *)
(*Checks *)


(* ::Text:: *)
(*Eq. (9)*)


Table[
	Sum[\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]], {\[Alpha]d, 2}] == 
	\[Delta][\[Alpha], \[Beta]] \[Delta][\[Mu], \[Nu]] + 2 I m[\[Mu], \[Nu]][\[Alpha], \[Beta]]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates
Table[
	Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d], {\[Alpha], 2}] == 
	\[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Mu], \[Nu]] + 2 I mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha]d, 2}, {\[Beta]d, 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (10)*)


Table[{
	Sum[
		\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]] + 
		\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]]
	, {\[Alpha]d, 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha], \[Beta]]
}, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates
Table[{
	Sum[
		\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d] + 
		\[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Mu]][\[Alpha], \[Beta]d]
	, {\[Alpha], 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha]d, \[Beta]d]
}, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha]d, 2}, {\[Beta]d, 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (14)*)


Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Mu], 0, d}] == 2 (d+1)


(* ::Section:: *)
(*Bulk Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations*)


Boson[\[ScriptCapitalD], \[ScriptCapitalP][_], \[ScriptCapitalK][_], \[ScriptCapitalM][_, _], \[ScriptCapitalR]];
Fermion[\[ScriptCapitalQ]p[_], \[ScriptCapitalQ]m[_], \[ScriptCapitalS]p[_], \[ScriptCapitalS]m[_]];

\[ScriptCapitalM][\[Mu]_, \[Nu]_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM][\[Nu], \[Mu]];
\[ScriptCapitalM][\[Mu]_, \[Mu]_] := 0;

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]], -I \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, d}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]], +I \[ScriptCapitalK][\[Mu]]], {\[Mu], 0, d}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Nu]], 2I (\[Delta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]])], {\[Mu], 0, d}, {\[Nu], 0, d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalM][\[Rho], \[Sigma]], I(
	+ \[Delta][\[Mu], \[Rho]] \[ScriptCapitalM][\[Nu], \[Sigma]]
	- \[Delta][\[Nu], \[Rho]] \[ScriptCapitalM][\[Mu], \[Sigma]]
	- \[Delta][\[Mu], \[Sigma]] \[ScriptCapitalM][\[Nu], \[Rho]]
	+ \[Delta][\[Nu], \[Sigma]] \[ScriptCapitalM][\[Mu], \[Rho]]
)], {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Rho], 0, d}, {\[Sigma], 0, d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]], I (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Rho], 0, d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]], I (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Rho], 0, d}];

Table[SetAntiCommutator[\[ScriptCapitalQ]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[\[CapitalSigma][\[Mu]][\[Alpha],\[Alpha]d] \[ScriptCapitalP][\[Mu]], {\[Mu], 0, d}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalS]m[\[Alpha]], Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalK][\[Mu]], {\[Mu], 0, d}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 
	+ \[Delta][\[Alpha], \[Beta]] (I \[ScriptCapitalD] - d/2 \[ScriptCapitalR]) 
	+ Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, d}, {\[Nu], 0, d}]]
, {\[Alpha], 2}, {\[Beta], 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalQ]m[\[Beta]d], 
	+ \[Delta][\[Alpha]d, \[Beta]d] (I \[ScriptCapitalD] + d/2 \[ScriptCapitalR]) 
	+ Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, d}, {\[Nu], 0, d}]]
, {\[Alpha]d, 2}, {\[Beta]d, 2}];

Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]p[\[Alpha]],  + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], 0, d}, {\[Alpha],  2}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]m[\[Alpha]d], + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]m[\[Alpha]] , {\[Alpha],  2}]], {\[Mu], 0, d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]p[\[Alpha]d], - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]p[\[Alpha]],  {\[Alpha],  2}]], {\[Mu], 0, d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]m[\[Alpha]],  - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]m[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], 0, d}, {\[Alpha] , 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]p[\[Alpha]], Sum[m[\[Mu], \[Nu]][\[Alpha], \[Beta]] \[ScriptCapitalQ]p[\[Beta]], {\[Beta], 2}]]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d] \[ScriptCapitalQ]m[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]p[\[Alpha]d], -Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalS]p[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]m[\[Alpha]], -Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalS]m[\[Beta]], {\[Beta], 2}]]
, {\[Mu], 0, d}, {\[Nu], 0, d}, {\[Alpha], 2}];

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
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, d}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, d}, {\[Nu], 0, d}],
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
	- 1/2 Sum[\[ScriptCapitalP][\[Mu]]\[CenterDot]\[ScriptCapitalK][\[Mu]] + \[ScriptCapitalK][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]], {\[Mu], 0, d}]
	+ 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, d}, {\[Nu], 0, d}]
	- d/4 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 Sum[\[ScriptCapitalS]p[\[Alpha]d]\[CenterDot]\[ScriptCapitalQ]m[\[Alpha]d] - \[ScriptCapitalQ]m[\[Alpha]d]\[CenterDot]\[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]
	+ 1/2 Sum[\[ScriptCapitalS]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]] - \[ScriptCapitalQ]p[\[Alpha]]\[CenterDot]\[ScriptCapitalS]m[\[Alpha]], {\[Alpha], 2}]
);
Table[Commutator[\[ScriptCapitalC]2, op], {op, allOperators}] // Expand // Flatten // DeleteDuplicates


(* ::Section:: *)
(*Boundary Algebra*)


(* ::Subsection::Closed:: *)
(*Embedding of OSP(1|4) subalgebra*)


(* ::Text:: *)
(*Check that the subalgebra closes:*)


Qs = {\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]};
Ss = {\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2]};
Conf = Flatten @ Join[
	{\[ScriptCapitalD]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, 2}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 1}, {\[Nu], \[Mu]+1, 2}]
];
allDefOps = Join[Conf, Qs, Ss];
defOpsToZero = Solve[allDefOps == 0, Join[Conf, {\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]p[2], \[ScriptCapitalS]p[1], \[ScriptCapitalS]p[2]}]] // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2def = ( 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 2}]
	+ 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
	+ 1/4 Commutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2]]
	- 1/4 Commutator[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates


(* ::Text:: *)
(*Casimir eigenvalue*)


(Expand[ 
	- \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 2}]
	+ 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
	+ 1/4 AntiCommutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2]]
	- 1/4 AntiCommutator[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]]
] /. {
	\[ScriptCapitalD] -> -I \[CapitalDelta],
	\[ScriptCapitalM][0,1]\[CenterDot]\[ScriptCapitalM][0,1] -> l(l+1) - \[ScriptCapitalM][0,2]\[CenterDot]\[ScriptCapitalM][0,2] - \[ScriptCapitalM][1,2]\[CenterDot]\[ScriptCapitalM][1,2],
	\[ScriptCapitalR] -> r
}) - (
	+ \[CapitalDelta](\[CapitalDelta]-2)
	+ l(l+1)
) // Expand


(* ::Subsection:: *)
(*Calculate blocks*)


(* ::Subsubsection:: *)
(* Ward identities*)


(* termMixed = {Qm1, [Qm2, \[Phi]]} *)
eqs = {
	(* Checked! *)
	+ AntiCommutator[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] 
	- termMixed
	- term[1, 1],
	(* Checked *)
	+ AntiCommutator[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] 
	- term[2, 1],
	(* Checked *)
	+ AntiCommutator[\[ScriptCapitalQ]p[2], \[ScriptCapitalQ]m[1]] 
	- term[1, 2],
	(* Checked *)
	+ AntiCommutator[\[ScriptCapitalQ]p[2], \[ScriptCapitalQ]m[2]] 
	- termMixed
	- term[2, 2],
	(* Not checked *)
	+ AntiCommutator[\[ScriptCapitalS]p[2] + \[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[1]] 
	- termMixed Sum[I x[1][\[Mu]] \[CapitalSigma]b[\[Mu]][2, 1], {\[Mu], 0, 3}]
	- I Sum[x[2][\[Mu]] \[CapitalSigma]b[\[Mu]][2, \[Alpha]] term[1, \[Alpha]],  {\[Mu], 0, 3}, {\[Alpha], 2}]
}  /. {
	\[ScriptCapitalD] :> -I (Sum[x[1][\[Mu]] \[ScriptD][1][\[Mu]], {\[Mu], 0, 2}] + \[CapitalDelta]p),
	\[ScriptCapitalR] :> \[CapitalDelta]p,
	\[ScriptCapitalP][\[Mu]_] :> -I \[ScriptD][1][\[Mu]],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> +I (x[1][\[Mu]] \[ScriptD][1][\[Nu]] - x[1][\[Nu]] \[ScriptD][1][\[Mu]])
};
rules = Solve[eqs == 0, {termMixed, term[1, 1], term[1, 2], term[2, 1], term[2, 2]}] // First


(* ::Subsubsection:: *)
(*Defect channel*)


(* ::Text:: *)
(*Terms surviving the Casimir*)


(
	+ 1/4 Commutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2]]
	- 1/4 Commutator[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]]
) - ( 
	- 1/2 \[ScriptCapitalQ]p[1]\[CenterDot]\[ScriptCapitalS]p[2]
	- 1/2 \[ScriptCapitalQ]m[2]\[CenterDot]\[ScriptCapitalS]p[2]
	+ 1/2 \[ScriptCapitalS]m[1]\[CenterDot]\[ScriptCapitalQ]p[1]
	+ 1/2 \[ScriptCapitalQ]p[2]\[CenterDot]\[ScriptCapitalS]p[1]
	- 1/2 \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]p[1]
	+ 1/2 \[ScriptCapitalS]m[2]\[CenterDot]\[ScriptCapitalQ]p[2]
	(* Relevant part *)
	- 1/2 \[ScriptCapitalQ]m[2]\[CenterDot]\[ScriptCapitalS]m[1]
	+ 1/2 \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]m[2]
) // Expand


diffOpDef = (
	1/2 I Sum[x[1][\[Mu]] (\[CapitalSigma]b[\[Mu]][2, 2] + \[CapitalSigma]b[\[Mu]][1, 1]), {\[Mu], 0, 3}] termMixed
	+ \[CapitalDelta]p id
) /. rules


(* ::Subsubsection:: *)
(*Bulk channel*)


(* ::Text:: *)
(*Contribution from bulk channel*)


terms = (
	+ I Sum[x[1][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term[\[Alpha]d, \[Alpha]], {\[Mu], 0, 3}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	- I Sum[x[2][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term[\[Alpha]d, \[Alpha]], {\[Mu], 0, 3}, {\[Alpha],  2}, {\[Alpha]d, 2}] 
) //. rules // ExpandAll // Simplify
