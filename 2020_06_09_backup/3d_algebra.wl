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


\[Delta] = KroneckerDelta;
\[Eta][0, 0] = -1;
\[Eta][1, 1] = \[Eta][2, 2] = +1;
\[Eta][\[Mu]_Integer, \[Nu]_Integer] = 0;

\[Epsilon]uu[1, 2] = -1; \[Epsilon]uu[2, 1] = +1;
\[Epsilon]uu[1, 1] = \[Epsilon]uu[2, 2] = 0;
\[Epsilon]dd[1, 2] = -1; \[Epsilon]dd[2, 1] = +1;
\[Epsilon]dd[1, 1] = \[Epsilon]dd[2, 2] = 0;
\[Epsilon]ddd[0, 1, 2] = \[Epsilon]ddd[1, 2, 0] = \[Epsilon]ddd[2, 0, 1] = +1;
\[Epsilon]ddd[1, 0, 2] = \[Epsilon]ddd[2, 1, 0] = \[Epsilon]ddd[0, 2, 1] = -1;
\[Epsilon]ddd[\[Mu]_Integer, \[Nu]_Integer, \[Rho]_Integer] = 0;
\[Epsilon]uuu[\[Mu]_, \[Nu]_, \[Rho]_] = \[Epsilon]ddd[\[Mu], \[Nu], \[Rho]];

\[Sigma]ud[i_Integer][\[Alpha]_Integer, \[Beta]_Integer] := PauliMatrix[i][[\[Alpha], \[Beta]]];
\[Gamma]ddu[0][\[Alpha]_, \[Beta]_] := I \[Sigma]ud[2][\[Alpha], \[Beta]];
\[Gamma]ddu[1][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[1][\[Alpha], \[Beta]];
\[Gamma]ddu[2][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[3][\[Alpha], \[Beta]];
\[Gamma]ddd[0][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[0][\[Alpha], \[Beta]];
\[Gamma]ddd[1][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[3][\[Alpha], \[Beta]];
\[Gamma]ddd[2][\[Alpha]_, \[Beta]_] := - \[Sigma]ud[1][\[Alpha], \[Beta]];
\[Gamma]duu[0][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[0][\[Alpha], \[Beta]];
\[Gamma]duu[1][\[Alpha]_, \[Beta]_] := - \[Sigma]ud[3][\[Alpha], \[Beta]];
\[Gamma]duu[2][\[Alpha]_, \[Beta]_] := + \[Sigma]ud[1][\[Alpha], \[Beta]];
\[Gamma]udu[\[Mu]_][\[Alpha]_, \[Beta]_] := \[Eta][\[Mu], \[Mu]] \[Gamma]ddu[\[Mu]][\[Alpha], \[Beta]];
\[Gamma]udd[\[Mu]_][\[Alpha]_, \[Beta]_] := \[Eta][\[Mu], \[Mu]] \[Gamma]ddd[\[Mu]][\[Alpha], \[Beta]];
\[Gamma]uuu[\[Mu]_][\[Alpha]_, \[Beta]_] := \[Eta][\[Mu], \[Mu]] \[Gamma]duu[\[Mu]][\[Alpha], \[Beta]];


(* ::Section::Closed:: *)
(*Bulk Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations*)


Boson[\[ScriptCapitalD], \[ScriptCapitalP][_], \[ScriptCapitalK][_], \[ScriptCapitalM][_, _], \[ScriptCapitalI][_, _]];
Fermion[\[ScriptCapitalQ][_,_], \[ScriptCapitalS][_,_]];

\[ScriptCapitalM][\[Mu]_, \[Nu]_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM][\[Nu], \[Mu]];
\[ScriptCapitalM][\[Mu]_, \[Mu]_] := 0;
\[ScriptCapitalI][a_, b_] /; a>b := -\[ScriptCapitalI][b, a];
\[ScriptCapitalI][\[Mu]_, \[Mu]_] := 0;

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]], +I \[ScriptCapitalP][\[Mu]]], {\[Mu], 0, 2}];

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]], -I \[ScriptCapitalK][\[Mu]]], {\[Mu], 0, 2}];

Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalK][\[Nu]], 2I (\[Eta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]])], {\[Mu], 0, 2}, {\[Nu], 0, 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalM][\[Rho], \[Sigma]], I(
	+ \[Eta][\[Mu], \[Rho]] \[ScriptCapitalM][\[Nu], \[Sigma]]
	- \[Eta][\[Nu], \[Rho]] \[ScriptCapitalM][\[Mu], \[Sigma]]
	- \[Eta][\[Mu], \[Sigma]] \[ScriptCapitalM][\[Nu], \[Rho]]
	+ \[Eta][\[Nu], \[Sigma]] \[ScriptCapitalM][\[Mu], \[Rho]]
)], {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}, {\[Sigma], 0, 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])]
, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}];

Table[SetCommutator[\[ScriptCapitalI][a, b], \[ScriptCapitalI][c, d], I(
	+ \[Delta][a, c] \[ScriptCapitalI][b, d]
	- \[Delta][b, c] \[ScriptCapitalI][a, d]
	- \[Delta][a, d] \[ScriptCapitalI][b, c]
	+ \[Delta][b, d] \[ScriptCapitalI][a, c]
)], {a, 2}, {b, 2}, {c, 2}, {d, 2}];

Table[SetAntiCommutator[\[ScriptCapitalQ][a, \[Alpha]], \[ScriptCapitalQ][b, \[Beta]], Sum[\[Eta][\[Mu], \[Mu]] \[Gamma]ddd[\[Mu]][\[Alpha], \[Beta]] \[ScriptCapitalP][\[Mu]] \[Delta][a, b], {\[Mu], 0, 2}]]
, {a, 2}, {b, 2}, {\[Alpha], 2}, {\[Beta], 2}];

Table[SetAntiCommutator[\[ScriptCapitalS][a, \[Alpha]], \[ScriptCapitalS][b, \[Beta]], Sum[\[Eta][\[Mu], \[Mu]] \[Gamma]ddd[\[Mu]][\[Alpha], \[Beta]] \[ScriptCapitalK][\[Mu]] \[Delta][a, b], {\[Mu], 0, 2}]]
, {a, 2}, {b, 2}, {\[Alpha], 2}, {\[Beta], 2}];

Table[SetAntiCommutator[\[ScriptCapitalI][a, b], \[ScriptCapitalQ][c, \[Alpha]], I (\[Delta][a, c] \[ScriptCapitalQ][b, \[Alpha]] - \[Delta][b, c] \[ScriptCapitalQ][a, \[Alpha]])]
, {a, 2}, {b, 2}, {c, 2}, {\[Alpha], 2}];

Table[SetAntiCommutator[\[ScriptCapitalI][a, b], \[ScriptCapitalS][c, \[Alpha]], I (\[Delta][a, c] \[ScriptCapitalS][b, \[Alpha]] - \[Delta][b, c] \[ScriptCapitalS][a, \[Alpha]])]
, {a, 2}, {b, 2}, {c, 2}, {\[Alpha], 2}];

Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ][A, a], Sum[\[Epsilon]up[A,B]\[Epsilon]dw[a,b]\[ScriptCapitalS][B,b],{B,2},{b,2}]],{A,2},{a,2}];


Table[SetAntiCommutator[\[ScriptCapitalQ][A,a],\[ScriptCapitalS][B,b],-2\[Delta][a,b]\[ScriptCapitalR][A,B]+\[Delta][A,B]\[ScriptCapitalM][a,b]+\[Delta][a,b]\[Delta][A,B]\[ScriptCapitalD]],{A,2},{B,2},{a,2},{b,2}];
Table[SetCommutator[\[ScriptCapitalD],\[ScriptCapitalQ][A,a],+1/2\[ScriptCapitalQ][A,a]],{A,2},{a,2}];
Table[SetCommutator[\[ScriptCapitalD],\[ScriptCapitalS][A,a],-1/2\[ScriptCapitalS][A,a]],{A,2},{a,2}];
Table[SetCommutator[\[ScriptCapitalP],\[ScriptCapitalS][A,a],-Sum[\[Epsilon]dw[A,B]\[Epsilon]up[a,b]\[ScriptCapitalQ][B,b],{B,2},{b,2}]],{A,2},{a,2}];
Table[SetCommutator[\[ScriptCapitalM][a,b],\[ScriptCapitalQ][C,c],\[Delta][c,b]\[ScriptCapitalQ][C,a]-1/2\[Delta][a,b]\[ScriptCapitalQ][C,c]],{C,2},{a,2},{b,2},{c,2}];
Table[SetCommutator[\[ScriptCapitalM][a,b],\[ScriptCapitalS][C,c],-(\[Delta][a,c]\[ScriptCapitalS][C,b]-1/2\[Delta][a,b]\[ScriptCapitalS][C,c])],{C,2},{a,2},{b,2},{c,2}];
Table[SetCommutator[\[ScriptCapitalR][A,B],\[ScriptCapitalQ][C,c],\[Delta][B,C]\[ScriptCapitalQ][A,c]-1/2\[Delta][A,B]\[ScriptCapitalQ][C,c]],{A,2},{B,2},{C,2},{c,2}];
Table[SetCommutator[\[ScriptCapitalR][A,B],\[ScriptCapitalS][C,c],-(\[Delta][A,C]\[ScriptCapitalS][B,c]-1/2\[Delta][A,B]\[ScriptCapitalS][C,c])],{A,2},{B,2},{C,2},{c,2}];


(* ::Subsection::Closed:: *)
(*Check Jacobi identities*)


allOperators = Flatten @ Join[
	{\[ScriptCapitalD]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, 2}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}],
	Table[\[ScriptCapitalI][a, b], {a, 2}, {b, 2}]
]; (*
,Table[{\[ScriptCapitalM][a,b],\[ScriptCapitalR][a,b],\[ScriptCapitalQ][a,b],\[ScriptCapitalS][a,b]},{a,2},{b,2}]}; *)
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
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]](\[ScriptCapitalP][\[Mu]]\[CenterDot]\[ScriptCapitalK][\[Mu]] + \[ScriptCapitalK][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]]), {\[Mu], 0, 2}]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]] \[Eta][\[Nu], \[Nu]] \[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Nu], \[Mu]], {\[Mu], 0, 2}, {\[Nu], 0, 2}]
);
Table[Commutator[\[ScriptCapitalC]2, op], {op, allOperators}] // Expand // Flatten // DeleteDuplicates


(* ::Section:: *)
(*Defect Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations*)


Join[
	Table[Commutator[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]]] == +I \[ScriptCapitalP][\[Mu]], {\[Mu], 0, 1}],
	Table[Commutator[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]]] == -I \[ScriptCapitalK][\[Mu]], {\[Mu], 0, 1}],
	Table[Commutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalK][\[Nu]]] == 2I (\[Eta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]]), {\[Mu], 0, 1}, {\[Nu], 0, 1}],
	Table[Commutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]]] == I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])
		, {\[Mu], 0, 1}, {\[Nu], 0, 1}, {\[Rho], 0, 1}],
	Table[Commutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]]] == I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])
		, {\[Mu], 0, 2}, {\[Nu], 0, 2}, {\[Rho], 0, 2}]
] // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Check Jacobi identities*)


allDefOperators = Flatten @ Join[
	{\[ScriptCapitalD]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 0, 1}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 0, 1}, {\[Nu], 0, 1}]
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
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]](\[ScriptCapitalP][\[Mu]]\[CenterDot]\[ScriptCapitalK][\[Mu]] + \[ScriptCapitalK][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]]), {\[Mu], 0, 1}]
	+ 1/2 Sum[\[Eta][\[Mu], \[Mu]] \[Eta][\[Nu], \[Nu]] \[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Nu], \[Mu]], {\[Mu], 0, 1}, {\[Nu], 0, 1}]
);
Table[Commutator[\[ScriptCapitalC]2, op], {op, allDefOperators}] // Expand // Flatten // DeleteDuplicates


(* ::Section:: *)
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


(* ::Section:: *)
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


(* ::Section:: *)
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
