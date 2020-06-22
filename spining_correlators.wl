(* ::Package:: *)

Quit


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


(* ::Subsection::Closed:: *)
(*Main (crap)*)


\[Delta] = KroneckerDelta;
MAct[\[Alpha]_, \[Beta]_][0] := 0;
MAct[\[Alpha]_, \[Beta]_][num_?NumericQ a_] := num MAct[\[Alpha], \[Beta]][a];
MAct[\[Alpha]_, \[Beta]_][a_ + b_] := MAct[\[Alpha], \[Beta]][a] + MAct[\[Alpha], \[Beta]][b];
MAct[\[Alpha]_, \[Beta]_][OO[\[Alpha]1_]] := 1/2 (
	+ 2 \[Delta][\[Alpha]1, \[Beta]] OO[\[Alpha]] 
	- \[Delta][\[Alpha], \[Beta]] OO[\[Alpha]1]
);


Table[
	lhs = MAct[\[Alpha], \[Beta]][MAct[\[Gamma], \[Sigma]][OO[\[Rho]]]] - MAct[\[Gamma], \[Sigma]][MAct[\[Alpha], \[Beta]][OO[\[Rho]]]];
	rhs = \[Delta][\[Gamma], \[Beta]] MAct[\[Alpha], \[Sigma]][OO[\[Rho]]] - \[Delta][\[Alpha], \[Sigma]] MAct[\[Gamma], \[Beta]][OO[\[Rho]]];
	lhs - rhs
, {\[Alpha], 2}, {\[Beta], 2}, {\[Gamma], 2}, {\[Sigma], 2}, {\[Rho], 2}] // Expand


(* ::Subsection:: *)
(*Define diff operators*)


(* ::Subsubsection::Closed:: *)
(*Define diff operators*)


Clear[MAct]
\[Delta] = KroneckerDelta;
MAct[\[Mu]_, \[Nu]_][0] := 0;
MAct[\[Mu]_, \[Nu]_][num_?NumericQ a_] := num MAct[\[Mu], \[Nu]][a];
MAct[\[Mu]_, \[Nu]_][a_ + b_] := MAct[\[Mu], \[Nu]][a] + MAct[\[Mu], \[Nu]][b];
MAct[\[Mu]_, \[Nu]_][OO[\[Rho]_]] := (
	- \[Delta][\[Mu], \[Rho]] OO[\[Nu]]
	+ \[Delta][\[Nu], \[Rho]] OO[\[Mu]]
);
MAct[\[Mu]_, \[Nu]_][\[Phi]] := 0
MAct[\[Mu]_, \[Nu]_][der[expr_, x[i_][\[Rho]_]]] := der[MAct[\[Mu], \[Nu]][expr], x[i][\[Rho]]]
MAct[\[Mu]_, \[Nu]_][num_?(FreeQ[#, OO]&) expr_] := num MAct[\[Mu], \[Nu]][expr]


SetNumeric[\[CapitalDelta][_], a];
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Delta][\[Mu], \[Nu]]
\[ScriptCapitalD]d[i_][expr_] := ( 
	+ Sum[x[i][\[Mu]] der[expr, x[i][\[Mu]]], {\[Mu], 3}]
	+ \[CapitalDelta][i] expr 
);
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := (
	- Sum[x[i][\[Nu]]^2, {\[Nu], 3}] der[expr, x[i][\[Mu]]] 
	+ 2 x[i][\[Mu]] Sum[x[i][\[Nu]] der[expr, x[i][\[Nu]]], {\[Nu], 3}] 
	+ 2 x[i][\[Mu]] \[CapitalDelta][i] expr
	- 2 Sum[x[i][\[Nu]] MAct[\[Mu], \[Nu]][expr], {\[Nu], 3}]
);
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := (
	- x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	+ x[i][\[Nu]] der[expr, x[i][\[Mu]]]
	+ MAct[\[Mu], \[Nu]][expr]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


comm[op1_, op2_][expr_] := op1[op2[expr]] - op2[op1[expr]]


Table[comm[\[ScriptCapitalD]d[1], \[ScriptCapitalP]d[\[Mu]][1]][OO[\[Nu]]] + \[ScriptCapitalP]d[\[Mu]][1][OO[\[Nu]]], {\[Mu], 3}, {\[Nu], 3}]
Table[comm[\[ScriptCapitalD]d[1], \[ScriptCapitalK]d[\[Mu]][1]][OO[\[Nu]]] - \[ScriptCapitalK]d[\[Mu]][1][OO[\[Nu]]], {\[Mu], 3}, {\[Nu], 3}] // Expand
Table[comm[\[ScriptCapitalK]d[\[Mu]][1], \[ScriptCapitalP]d[\[Nu]][1]][OO[\[Rho]]] + 2 \[Delta][\[Mu], \[Nu]] \[ScriptCapitalD]d[1][OO[\[Rho]]] - 2 \[ScriptCapitalM]d[\[Mu], \[Nu]][1][OO[\[Rho]]]
, {\[Mu], 3}, {\[Nu], 3}, {\[Rho], 3}] // Expand
Table[comm[\[ScriptCapitalM]d[\[Mu], \[Nu]][1], \[ScriptCapitalM]d[\[Rho], \[Sigma]][1]][OO[\[Theta]]] + (
	+ \[Delta][\[Nu], \[Rho]] \[ScriptCapitalM]d[\[Mu], \[Sigma]][1][OO[\[Theta]]] - \[Delta][\[Mu], \[Rho]] \[ScriptCapitalM]d[\[Nu], \[Sigma]][1][OO[\[Theta]]] 
	+ \[Delta][\[Mu], \[Sigma]] \[ScriptCapitalM]d[\[Nu], \[Rho]][1][OO[\[Theta]]] - \[Delta][\[Nu], \[Sigma]] \[ScriptCapitalM]d[\[Mu], \[Rho]][1][OO[\[Theta]]]
), {\[Mu], 2}, {\[Nu], 2}, {\[Rho], 2}, {\[Sigma], 2}, {\[Theta], 2}] // Expand
Table[comm[\[ScriptCapitalM]d[\[Mu], \[Nu]][1], \[ScriptCapitalP]d[\[Rho]][1]][OO[\[Theta]]] + (
	+ \[Delta][\[Nu], \[Rho]] \[ScriptCapitalP]d[\[Mu]][1][OO[\[Theta]]] - \[Delta][\[Mu], \[Rho]] \[ScriptCapitalP]d[\[Nu]][1][OO[\[Theta]]]
), {\[Mu], 2}, {\[Nu], 2}, {\[Rho], 2}, {\[Theta], 2}] // Expand
(* The error here probably has to do with how we act, we should let symmetry 
   generator get past derivatives and then replace by differential operator *)
Table[comm[\[ScriptCapitalM]d[\[Mu], \[Nu]][1], \[ScriptCapitalK]d[\[Rho]][1]][OO[\[Theta]]] + (
	+ \[Delta][\[Nu], \[Rho]] \[ScriptCapitalK]d[\[Mu]][1][OO[\[Theta]]] - \[Delta][\[Mu], \[Rho]] \[ScriptCapitalK]d[\[Nu]][1][OO[\[Theta]]]
), {\[Mu], 2}, {\[Nu], 2}, {\[Rho], 2}, {\[Theta], 2}] // Expand


(* ::Subsubsection::Closed:: *)
(*Check < O\[Mu] O\[Mu] > no defect*)


inv[\[Mu]_, \[Nu]_][x_] := \[Delta][\[Mu], \[Nu]] - 2 x[\[Mu]] x[\[Nu]] / sq[x];
sq[x_] := Sum[x[\[Mu]]^2, {\[Mu], 3}]
x[1, 2][\[Mu]_] := x[1][\[Mu]] - x[2][\[Mu]]


Clear[twoPtFun]
pref = sq[x[1, 2]]^\[CapitalDelta][1];
twoPtFun[\[Mu]_, \[Nu]_] := inv[\[Mu], \[Nu]][x[1, 2]] / pref;
Table[{
	(\[ScriptCapitalD]d[1][\[Phi]] + \[ScriptCapitalD]d[2][\[Phi]] /. \[Phi] -> twoPtFun[\[Mu], i]) / twoPtFun[\[Mu], i],
	(\[ScriptCapitalP]d[3][1][\[Phi]] + \[ScriptCapitalP]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun[\[Mu], i]) / twoPtFun[\[Mu], i]
}, {\[Mu], 3}, {i, 2}] /. \[CapitalDelta][_] -> \[CapitalDelta] // Expand // Together // Simplify


{\[Mu], \[Nu]} = {1, 2};
term1 = (\[ScriptCapitalM]d[1, 2][1][OO[\[Mu]]] /. OO[\[Rho]_] :> twoPtFun[\[Rho], \[Nu]]) pref // ExpandAll;
term2 = (\[ScriptCapitalM]d[1, 2][2][OO[\[Nu]]] /. OO[\[Rho]_] :> twoPtFun[\[Mu], \[Rho]]) pref // ExpandAll;
term1 + term2 /. \[CapitalDelta][_] -> \[CapitalDelta] // Together // FullSimplify


{\[Mu], \[Nu]} = {1, 2};
term1 = (\[ScriptCapitalK]d[3][1][OO[\[Mu]]] /. OO[\[Rho]_] :> twoPtFun[\[Rho], \[Nu]]) pref // ExpandAll;
term2 = (\[ScriptCapitalK]d[3][2][OO[\[Nu]]] /. OO[\[Rho]_] :> twoPtFun[\[Mu], \[Rho]]) pref // ExpandAll;
term1 + term2 /. \[CapitalDelta][_] -> \[CapitalDelta] // Together // FullSimplify


(* ::Subsubsection::Closed:: *)
(*Check <\[Phi] O>*)


xorth2 = x[1][1]^2 + x[1][2]^2;
x12par = x[1][3] - x[2][3];
twoPtFun = 1 / (
	(xorth2 + x12par^2)^\[CapitalDelta][2]
	(xorth2)^((\[CapitalDelta][1]-\[CapitalDelta][2])/2)
);


(\[ScriptCapitalD]d[1][\[Phi]] + \[ScriptCapitalD]d[2][\[Phi]] /. \[Phi] -> twoPtFun) / twoPtFun // Expand // Together // Simplify
(\[ScriptCapitalP]d[3][1][\[Phi]] + \[ScriptCapitalP]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun) / twoPtFun // Expand // Together // Simplify
(\[ScriptCapitalM]d[1, 2][1][\[Phi]] + \[ScriptCapitalM]d[1,2][2][\[Phi]] /. \[Phi] -> twoPtFun) / twoPtFun // Expand // Together // Simplify
(\[ScriptCapitalK]d[3][1][\[Phi]] + \[ScriptCapitalK]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun) / twoPtFun /. x[2][1|2] -> 0 // Expand // Together // Simplify


(* ::Subsubsection::Closed:: *)
(*Check < O\[Mu] Oi >*)


Clear[twoPtFun]
pref = (xorth2 + x12par^2)^(\[CapitalDelta][2]+1) (xorth2)^((\[CapitalDelta][1]-\[CapitalDelta][2])/2);
twoPtFun[a_, j_] /; a==3 && 1<=j<=2 := (x[1][a]-x[2][a]) x[1][j] / pref;
twoPtFun[i_, j_] /; 1<=i<=2 && 1<=j<=2 := x[1][i] x[1][j] / pref;
twoPtFun[\[Mu]_, 3] := 0;
Table[{
	(\[ScriptCapitalD]d[1][\[Phi]] + \[ScriptCapitalD]d[2][\[Phi]] /. \[Phi] -> twoPtFun[\[Mu], i]) / twoPtFun[\[Mu], i],
	(\[ScriptCapitalP]d[3][1][\[Phi]] + \[ScriptCapitalP]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun[\[Mu], i]) / twoPtFun[\[Mu], i]
}, {\[Mu], 3}, {i, 2}] // Expand // Together // Simplify


{\[Mu], i} = {1, 1};
lhs = (\[ScriptCapitalM]d[1, 2][1][OO[\[Mu]]] /. OO[\[Nu]_] :> twoPtFun[\[Nu], i]) pref // ExpandAll
rhs = (\[ScriptCapitalM]d[1, 2][2][OO[i]] /. OO[j_] :> twoPtFun[\[Mu], j]) pref // ExpandAll
lhs + rhs /. x[2][1|2] :> 0 


{\[Mu], i} = {1, 1};
lhs = (\[ScriptCapitalK]d[3][1][OO[\[Mu]]] /. OO[\[Nu]_] :> twoPtFun[\[Nu], i]) pref // ExpandAll;
rhs = (\[ScriptCapitalK]d[3][2][OO[i]] /. OO[j_] :> twoPtFun[\[Mu], j]) pref // ExpandAll;
lhs + rhs /. x[2][1|2] :> 0 // Together


(* ::Subsubsection:: *)
(*Check < \[Phi] Oi >*)


Clear[twoPtFun]
twoPtFun[i_] := x[1][i] / (
	(xorth2 + x12par^2)^\[CapitalDelta][2]
	(xorth2)^((\[CapitalDelta][1]-\[CapitalDelta][2]+1)/2)
);
Table[{
	(\[ScriptCapitalD]d[1][\[Phi]] + \[ScriptCapitalD]d[2][\[Phi]] /. \[Phi] -> twoPtFun[i]) / twoPtFun[i] // Expand // Together // Simplify,
	(\[ScriptCapitalP]d[3][1][\[Phi]] + \[ScriptCapitalP]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun[i]) / twoPtFun[i] // Expand // Together // Simplify
}, {i, 2}]


i = 1;
(\[ScriptCapitalM]d[1, 2][1][\[Phi]] + \[ScriptCapitalM]d[1, 2][2][OO[i]] /. {\[Phi] -> twoPtFun[i], OO[j_] :> twoPtFun[j]}) / twoPtFun[i];
% /. x[2][1|2] -> 0 // ExpandAll


i = 1;
(\[ScriptCapitalK]d[3][1][\[Phi]] + \[ScriptCapitalK]d[3][2][OO[i]] /. {\[Phi] -> twoPtFun[i], OO[j_] :> twoPtFun[j]}) / twoPtFun[i];
% /. x[2][1|2] -> 0 // ExpandAll // Together


(* ::Subsubsection:: *)
(*Check < \[Phi] Oi > with U(1)*)


Clear[twoPtFun]
twoPtFun[i_] := x[1][i] / (
	(xorth2 + x12par^2)^\[CapitalDelta][2]
	(xorth2)^((\[CapitalDelta][1]-\[CapitalDelta][2]+1)/2)
);
Table[{
	(\[ScriptCapitalD]d[1][\[Phi]] + \[ScriptCapitalD]d[2][\[Phi]] /. \[Phi] -> twoPtFun[i]) / twoPtFun[i] // Expand // Together // Simplify,
	(\[ScriptCapitalP]d[3][1][\[Phi]] + \[ScriptCapitalP]d[3][2][\[Phi]] /. \[Phi] -> twoPtFun[i]) / twoPtFun[i] // Expand // Together // Simplify
}, {i, 2}]


RAct[OO[\[Rho]_]] := rh OO[\[Rho]];
RAct[\[Phi]] := rp \[Phi];
transRot[i_][expr_] := \[ScriptCapitalM]d[1, 2][i][expr] + I RAct[expr];
i = 1;
(transRot[1][\[Phi]] + transRot[2][OO[i]] /. {\[Phi] -> twoPtFun[i], OO[j_] :> twoPtFun[j]}) / twoPtFun[i];
% /. x[2][1|2] -> 0 // ExpandAll


i = 1;
(\[ScriptCapitalK]d[3][1][\[Phi]] + \[ScriptCapitalK]d[3][2][OO[i]] /. {\[Phi] -> twoPtFun[i], OO[j_] :> twoPtFun[j]}) / twoPtFun[i];
% /. x[2][1|2] -> 0 // ExpandAll // Together
