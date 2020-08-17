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


(* ::Text:: *)
(**)


(* ::Section:: *)
(*Boundary blocks*)


(* ::Subsection:: *)
(*Compute non-susy blocks*)


(* ::Subsubsection::Closed:: *)
(*General*)


get$ia := ia[Unique[]]
get$id := id[Unique[]]
randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}


SetAttributes[dot, Orderless];
x2[i_, j_] := dot[x[i], x[i]] - 2 dot[x[i], x[j]] + dot[x[j], x[j]];


der[(\[CapitalDelta][_]|\[Eta][__]|d), x[_][_]] := 0
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Eta][\[Mu], \[Nu]]
der[dot[x[i_], x[j_]], x[k_][\[Mu]_]] := \[Delta][i, k] x[j][\[Mu]] + \[Delta][j, k] x[i][\[Mu]];
der[f[\[Xi]], x[i_][\[Mu]_]] := f'[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];
der[f'[\[Xi]], x[i_][\[Mu]_]] := f''[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];


\[ScriptCapitalD]d[i_][expr_] := With[{\[Mu] = get$ia}, ( x[i][\[Mu]] der[expr, x[i][\[Mu]]] + \[CapitalDelta][i] expr )];
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := With[{\[Nu] = get$ia}, -(
	+ dot[x[i], x[i]] der[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] x[i][\[Nu]] der[expr, x[i][\[Nu]]]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
)];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -(
	+ x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


\[Delta] = KroneckerDelta;


\[Xi]v = x2[1, 2] / (4 x[1][d] x[2][d]);
twoPtFunDef = (
	(2 x[1][d])^(-\[CapitalDelta][1]) 
	(2 x[2][d])^(-\[CapitalDelta][2])
	f[\[Xi]]
);


Clear[\[Eta]]
SetAttributes[\[Eta], Orderless]
\[Eta] /: \[Eta][d, d] := 1
\[Eta] /: \[Eta][d, \[Mu]_id] := 0
\[Eta] /: \[Eta][\[Mu]_ia, \[Mu]_ia] := d
\[Eta] /: \[Eta][\[Mu]_ia, \[Nu]_ia]^2 := d
\[Eta] /: \[Eta][\[Mu]_id, \[Mu]_id] := d-1
\[Eta] /: \[Eta][\[Mu]_id, \[Nu]_id]^2 := d-1
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] \[Eta][\[Nu]_ia, \[Rho]_] := \[Eta][\[Mu], \[Rho]]
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] der[f_, x[i_][\[Nu]_ia]] := der[f, x[i][\[Mu]]]


x /: x[i_][\[Mu]_ia]^2 := dot[x[i], x[i]]
x /: x[i_][\[Mu]_id]^2 := dot[x[i], x[i]] - x[i][d]^2
x /: x[i_][\[Mu]_ia] x[j_][\[Mu]_ia] := dot[x[i], x[j]]
x /: x[i_][\[Mu]_id] x[j_][\[Mu]_id] := dot[x[i], x[j]] - x[i][d] x[j][d]
x /: \[Eta][\[Mu]_, \[Nu]_ia] x[i_][\[Nu]_ia] := x[i][\[Mu]]
x /: \[Eta][\[Mu]_id, \[Nu]_id] x[i_][\[Nu]_id] := x[i][\[Mu]]


(* ::Subsubsection:: *)
(*Boundary channel*)


Clear[\[ScriptCapitalC]2def]
\[ScriptCapitalC]2def[i__][expr_] := With[{\[Mu] = get$id, \[Nu] = get$id}, 
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	- 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];


defBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta] - d/2 + 1, 2\[CapitalDelta] + 2 - d, -1/\[Xi]]
bulkBlock[\[CapitalDelta]_, \[CapitalDelta]12_, d_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[(\[CapitalDelta]+\[CapitalDelta]12)/2, (\[CapitalDelta]-\[CapitalDelta]12)/2, \[CapitalDelta]+1-d/2, -\[Xi]];


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-d+1);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2def[1][twoPtFunDef] - \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = f[\[Xi]] expr /. restore\[Xi] // Collect[#, f_[\[Xi]], Factor] &
expr /. f -> defBlock[\[CapitalDelta], d] // FullSimplify


(* ::Subsubsection:: *)
(*Bulk channel*)


Clear[\[ScriptCapitalC]2bulk]
\[ScriptCapitalC]2bulk[i__][expr_] := With[{\[Mu] = get$ia, \[Nu] = get$ia}, 
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	- 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-d);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2bulk[1, 2][twoPtFunDef] - \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = expr /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Simplify] &;
expr // Collect[#, f_[\[Xi]], Simplify] &
(\[Xi]^(-(\[CapitalDelta]/2)+\[CapitalDelta][1]/2+\[CapitalDelta][2]/2) expr / (4\[Xi]) 
	/. f -> (#^(-1/2(\[CapitalDelta][1]+\[CapitalDelta][2])) g[#] &) 
	/. g -> bulkBlock[\[CapitalDelta], \[CapitalDelta][1]-\[CapitalDelta][2], d]
	/. randRules[\[CapitalDelta], \[CapitalDelta][1], \[CapitalDelta][2], d, \[Xi]]
)


(* ::Text:: *)
(*Convenient form for later*)


expr /. {d -> 3, \[CapitalDelta][_] -> \[CapitalDelta]p} // Collect[#, f_[\[Xi]], Simplify] &
expr /. {d -> 4, \[CapitalDelta][_] -> \[CapitalDelta]p} // Collect[#, f_[\[Xi]], Simplify] &


(* ::Subsection::Closed:: *)
(*(2,0) boundary in d=3*)


(* ::Subsubsection:: *)
(*General*)


x2[i_, j_] := dot[x[i], x[i]] - 2 dot[x[i], x[j]] + dot[x[j], x[j]];
\[Xi]v = x2[1, 2] / (4 x[1][d] x[2][d]);
twoPtFunDef = (
	(2 x[1][d])^(-\[CapitalDelta][1]) 
	(2 x[2][d])^(-\[CapitalDelta][2])
	f[\[Xi]]
);


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 3}], d -> 3};
restoreInv = Solve[inv == \[Xi], x[1][1]] // First;
pref = (2 x[1][3])^(-\[CapitalDelta][1]) (2 x[2][3])^(-\[CapitalDelta][2]);


(* ::Subsubsection:: *)
(*Bulk channel*)


expr = (
4 id \[CapitalDelta]p-(x[1][1]-x[2][1]) (\[ScriptD][1][1]-I \[ScriptD][1][2])-I (x[1][2]-x[2][2]) (\[ScriptD][1][1]-I \[ScriptD][1][2])
-(x[1][3]-x[2][3]) \[ScriptD][1][3]-1/x[2][3] (x[1][3]-x[2][3]) (2 \[CapitalDelta]p+x[1][1] \[ScriptD][1][1]+I x[1][2] \[ScriptD][1][1]
-x[2][1] \[ScriptD][1][1]-I x[2][2] \[ScriptD][1][1]-I x[1][1] \[ScriptD][1][2]+x[1][2] \[ScriptD][1][2]
+I x[2][1] \[ScriptD][1][2]-x[2][2] \[ScriptD][1][2]+x[1][3] \[ScriptD][1][3])+1/x[2][3] (x[1][1]-x[2][1]) (-x[1][3] \[ScriptD][1][1]
-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])
-1/x[2][3] I (x[1][2]-x[2][2]) (-x[1][3] \[ScriptD][1][1]-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]
-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])
) /. {
	\[ScriptD][i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]],
	id :> pref f[inv]
};
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


(* ::Subsubsection:: *)
(*Bulk channel*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 2}], d -> 2};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][2])^(-\[CapitalDelta][1]) (2 x[2][2])^(-\[CapitalDelta][2]);


expr = (4 id \[CapitalDelta]p-(x[1][1]-x[2][1]) (\[ScriptD][1][1]-I \[ScriptD][1][2])-I (x[1][2]-x[2][2]) (\[ScriptD][1][1]-I \[ScriptD][1][2])-(x[1][3]-x[2][3]) \[ScriptD][1][3]-1/x[2][3] (x[1][3]-x[2][3]) (2 \[CapitalDelta]p+x[1][1] \[ScriptD][1][1]+I x[1][2] \[ScriptD][1][1]-x[2][1] \[ScriptD][1][1]-I x[2][2] \[ScriptD][1][1]-I x[1][1] \[ScriptD][1][2]+x[1][2] \[ScriptD][1][2]+I x[2][1] \[ScriptD][1][2]-x[2][2] \[ScriptD][1][2]+x[1][3] \[ScriptD][1][3])+1/x[2][3] (x[1][1]-x[2][1]) (-x[1][3] \[ScriptD][1][1]-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])-1/x[2][3] I (x[1][2]-x[2][2]) (-x[1][3] \[ScriptD][1][1]-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (\[Xi]+1) f''[\[Xi]]
	+ 2 \[Xi] (4 \[CapitalDelta]p (\[Xi] + 1) + 2 \[Xi] - 1) f'[\[Xi]]
	+ ( 2\[CapitalDelta]p(2\[CapitalDelta]p(\[Xi]+1) - 3) - \[CapitalDelta](\[CapitalDelta]-3)) f[\[Xi]]
	+ 4 \[Xi] (\[Xi] + 1) f'[\[Xi]] + 4 \[CapitalDelta]p (\[Xi] + 1) f[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


expr = (
	-((d[1][0] x[1][0] x[1][2])/(x[1][2]+x[2][2]))
	-(I d[1][1] x[1][0] x[1][2])/(x[1][2]+x[2][2])
	+(I d[1][0] x[1][1] x[1][2])/(x[1][2]+x[2][2])
	-(d[1][1] x[1][1] x[1][2])/(x[1][2]+x[2][2])
	-(d[1][2] x[1][2]^2)/(x[1][2]+x[2][2])
	+(d[1][0] x[1][2] x[2][0])/(x[1][2]+x[2][2])
	+(I d[1][1] x[1][2] x[2][0])/(x[1][2]+x[2][2])
	-(I d[1][0] x[1][2] x[2][1])/(x[1][2]+x[2][2])
	+(d[1][1] x[1][2] x[2][1])/(x[1][2]+x[2][2])
	+(d[1][2] x[1][2] x[2][2])/(x[1][2]+x[2][2])
	-(2 \[CapitalDelta]p x[1][2])/(x[1][2]+x[2][2]) pref f[inv]
	+ \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	- \[Xi] f'[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	-d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	2 d == c,
	(-(1/2)-2 d) == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


diffEqf /. f -> (#^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-1/2, 2\[CapitalDelta], -1/#] &) // FullSimplify


(* ::Subsection::Closed:: *)
(*(1,1) boundary in d=3*)


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


expr = (1/(x[1][2]+x[2][2]) (
	+2 I d[1][1] x[1][0] x[1][2]
	+4 d[1][1] x[1][1] x[1][2]
	+4 d[1][2] x[1][2]^2
	-2 I d[1][1] x[1][2] x[2][0]
	-4 d[1][1] x[1][2] x[2][1]
	-2 I d[1][1] x[1][0] x[2][2]
	-4 d[1][2] x[1][2] x[2][2]
	+2 I d[1][1] x[2][0] x[2][2]
	+d[1][0] (
		4 x[1][0] x[1][2]-2 I (x[1][2] (-2 I x[2][0]-x[2][1])
		+x[1][1] (x[1][2]-x[2][2])+x[2][1] x[2][2])
	)
	+4 \[CapitalDelta]p (x[1][2]-x[2][2]) pref f[inv]
)
	+ 4 \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (\[Xi]+1) f''[\[Xi]]
	+ 2 \[Xi] (4 \[CapitalDelta]p (\[Xi] + 1) + 2 \[Xi] - 1) f'[\[Xi]]
	+ ( 2\[CapitalDelta]p(2\[CapitalDelta]p(\[Xi]+1) - 3) - \[CapitalDelta](\[CapitalDelta]-3)) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] Derivative[1][f][\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	+ (-1/2 r^2 + r) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- (1/2(1/2-1) - 1/2(r-1)^2) f[\[Xi]]
) // Collect[#, G_[\[Xi]], Factor] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	3/4-2 d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	-1+2 d == c,
	-(1/2)-2 d == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*OSp(1|4) boundary in d=4*)


(* ::Subsubsection:: *)
(*General*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 4}], d -> 4};
restoreInv = Solve[inv == \[Xi], x[1][1]] // First;
pref = (2 x[1][4])^(-\[CapitalDelta][1]) (2 x[2][4])^(-\[CapitalDelta][2]);


(* ::Subsubsection:: *)
(*Bulk channel*)


expr = (
4 id \[CapitalDelta]p-(x[1][1]-x[2][1]) (\[ScriptD][1][1]-I \[ScriptD][1][2])-I (x[1][2]-x[2][2]) (\[ScriptD][1][1]-I \[ScriptD][1][2])
-(x[1][3]-x[2][3]) \[ScriptD][1][3]-1/x[2][3] (x[1][3]-x[2][3]) (2 \[CapitalDelta]p+x[1][1] \[ScriptD][1][1]+I x[1][2] \[ScriptD][1][1]
-x[2][1] \[ScriptD][1][1]-I x[2][2] \[ScriptD][1][1]-I x[1][1] \[ScriptD][1][2]+x[1][2] \[ScriptD][1][2]
+I x[2][1] \[ScriptD][1][2]-x[2][2] \[ScriptD][1][2]+x[1][3] \[ScriptD][1][3])+1/x[2][3] (x[1][1]-x[2][1]) (-x[1][3] \[ScriptD][1][1]
-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])
-1/x[2][3] I (x[1][2]-x[2][2]) (-x[1][3] \[ScriptD][1][1]-I x[1][3] \[ScriptD][1][2]+x[1][1] \[ScriptD][1][3]+I x[1][2] \[ScriptD][1][3]
-x[2][1] \[ScriptD][1][3]-I x[2][2] \[ScriptD][1][3])
) /. {
	\[ScriptD][i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]],
	id :> pref f[inv]
};
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (1+\[Xi]) f''[\[Xi]]
	+ 4 \[Xi] (-1+\[Xi]+2 \[CapitalDelta]p (1+\[Xi])) f'[\[Xi]]
	+ (4 \[CapitalDelta]-\[CapitalDelta]^2+4 \[CapitalDelta]p (-2+\[CapitalDelta]p+\[CapitalDelta]p \[Xi])) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] f'[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


expr = (id \[CapitalDelta]p-(x[1][3] (-I x[1][2] \[ScriptD][1][0]
+x[1][3] \[ScriptD][1][0]+I x[2][2] \[ScriptD][1][0]-x[2][3] \[ScriptD][1][0]+x[1][2] \[ScriptD][1][1]
+I x[1][3] \[ScriptD][1][1]-x[2][2] \[ScriptD][1][1]-I x[2][3] \[ScriptD][1][1]+I x[1][0] \[ScriptD][1][2]
-x[1][1] \[ScriptD][1][2]-I x[2][0] \[ScriptD][1][2]+x[2][1] \[ScriptD][1][2]-x[1][0] \[ScriptD][1][3]
-I x[1][1] \[ScriptD][1][3]+x[2][0] \[ScriptD][1][3]+I x[2][1] \[ScriptD][1][3]))/(x[1][0]
+I x[1][1]-x[2][0]-I x[2][1])
) /. {
	\[ScriptD][i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]],
	id :> pref f[inv]
};
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- (1/2(1/2-1) - 1/2(r-1)^2) f[\[Xi]]
) // Collect[#, G_[\[Xi]], Factor] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	3/4-2 d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	-1+2 d == c,
	-(1/2)-2 d == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


(* ::Subsection:: *)
(*Accross dimensions*)


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


bulkBlock[\[CapitalDelta]_, \[CapitalDelta]1_, \[CapitalDelta]2_, d_][\[Xi]_] :=(
	\[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[(\[CapitalDelta]+\[CapitalDelta]1-\[CapitalDelta]2)/2, (\[CapitalDelta]-\[CapitalDelta]1+\[CapitalDelta]2)/2, \[CapitalDelta]+1-d/2, -\[Xi]]
);
bulkSusyBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2, \[CapitalDelta]/2, \[CapitalDelta]+2-d/2, -\[Xi]]


diffEqf = (
	+ 4 \[Xi]^2 (1+\[Xi]) f''[\[Xi]]
	+ (-2 d \[Xi]+4 (1+2 \[CapitalDelta]p) \[Xi] (1+\[Xi])) f'[\[Xi]]
	+ (-\[CapitalDelta]^2+d (\[CapitalDelta]-2 \[CapitalDelta]p)+4 \[CapitalDelta]p^2 (1+\[Xi])) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] f'[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG /. G -> bulkSusyBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], \[Xi], d]
(* DSolve[diffEqG == 0, G[\[Xi]], \[Xi]] *)


diff = (
	+ bulkSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		+ bulkBlock[\[CapitalDelta], 0, 0, d][\[Xi]]
		+ \[CapitalDelta]^2 / ( (2\[CapitalDelta] - d + 2) (2\[CapitalDelta] - d + 4) ) bulkBlock[\[CapitalDelta]+2, 0, 0, d][\[Xi]]
	)
) /. randRules[\[CapitalDelta], d, \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


defectBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], (2-d+2 \[CapitalDelta])/2, 2\[CapitalDelta]-d+2, -1/\[Xi]];
defectSusyBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], (2-d+2 \[CapitalDelta])/2, 2\[CapitalDelta]-d+3, -1/\[Xi]];


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
) /. f -> defectBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], d, \[Xi]]


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- \[Xi] f'[\[Xi]]
) /. f -> defectSusyBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], d, \[Xi]]


diff = (
	+ defectSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		defectBlock[\[CapitalDelta], d][\[Xi]]
		+ \[CapitalDelta] / (4\[CapitalDelta] - 2d + 6) defectBlock[\[CapitalDelta]+1, d][\[Xi]]
	)
) /. randRules[\[CapitalDelta], d, \[Xi]]


(* ::Text:: *)
(*Code to find the solutions*)


(* diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) (f^\[Prime])[\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
) // Collect[#, f_[\[Xi]], Factor] &
(z^(-e-1) diffEqf /. f -> ((-1/#)^e ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &
sol = Solve[{
	(e-\[CapitalDelta]) (1-d+e+\[CapitalDelta]) == 0,
	1/2 e (d-2 (1+e)) == - a b,
	2-d+2 e == c,
	1/2 (d-4 (1+e))  == -(a + b + 1)
}, {a, b, c, e}];
\[Xi]^(-e) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates *)


(* ::Section:: *)
(*Defect blocks*)


(* ::Subsection:: *)
(*Compute non-susy blocks*)


(* ::Subsubsection::Closed:: *)
(*General*)


randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}


\[Delta] = KroneckerDelta;
get$ia := ia[Unique[]]
get$id := id[Unique[]]
get$io := io[Unique[]]


SetAttributes[dota, Orderless];
SetAttributes[doto, Orderless];
xa2[i_, j_] := dota[x[i], x[i]] - 2 dota[x[i], x[j]] + dota[x[j], x[j]];
\[Xi]v = xa2[1, 2] / (doto[x[1], x[1]] doto[x[2], x[2]])^(1/2);
\[Chi]v = (xa2[1, 2] + 2 doto[x[1], x[2]]) / (doto[x[1], x[1]] doto[x[2], x[2]])^(1/2);
\[Eta]v = doto[x[1], x[2]] / (doto[x[1], x[1]] doto[x[2], x[2]])^(1/2);
twoPtFun\[Xi]\[Eta] = (
	doto[x[1], x[1]]^(-\[CapitalDelta][1]/2)
	doto[x[2], x[2]]^(-\[CapitalDelta][2]/2)
	f[\[Xi], \[Eta]]
);
twoPtFun\[Chi]\[Eta] = (
	doto[x[1], x[1]]^(-\[CapitalDelta][1]/2)
	doto[x[2], x[2]]^(-\[CapitalDelta][2]/2)
	f[\[Chi], \[Eta]]
);


der[(\[CapitalDelta][_]|\[Eta][__]|d), x[_][_]] := 0
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Eta][\[Mu], \[Nu]]
der[dota[x[i_], x[j_]], x[k_][\[Mu]_]] := With[{\[Nu] = get$ia},
	\[Delta][i, k] \[Eta][\[Mu], \[Nu]] x[j][\[Nu]] + \[Delta][j, k] \[Eta][\[Mu], \[Nu]] x[i][\[Nu]]
];
der[doto[x[i_], x[j_]], x[k_][\[Mu]_]] := With[{\[Nu] = get$io},
	\[Delta][i, k] \[Eta][\[Mu], \[Nu]] x[j][\[Nu]] + \[Delta][j, k] \[Eta][\[Mu], \[Nu]] x[i][\[Nu]]
];
der[f_[\[Xi], \[Eta]], x[i_][\[Mu]_]] := (
	+ D[f[\[Xi], \[Eta]], \[Xi]] der[\[Xi]v, x[i][\[Mu]]]
	+ D[f[\[Xi], \[Eta]], \[Eta]] der[\[Eta]v, x[i][\[Mu]]]
);
der[f_[\[Chi], \[Eta]], x[i_][\[Mu]_]] := (
	+ D[f[\[Chi], \[Eta]], \[Chi]] der[\[Chi]v, x[i][\[Mu]]]
	+ D[f[\[Chi], \[Eta]], \[Eta]] der[\[Eta]v, x[i][\[Mu]]]
);


\[ScriptCapitalD]d[i_][expr_] := With[{\[Mu] = get$ia}, ( x[i][\[Mu]] der[expr, x[i][\[Mu]]] + \[CapitalDelta][i] expr )];
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := With[{\[Nu] = get$ia}, -(
	+ dota[x[i], x[i]] der[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] x[i][\[Nu]] der[expr, x[i][\[Nu]]]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
)];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -(
	+ x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


Clear[\[Eta]]
SetAttributes[\[Eta], Orderless]
\[Eta][\[Mu]_io, \[Nu]_id] := 0
\[Eta] /: \[Eta][\[Mu]_ia, \[Mu]_ia]   := d
\[Eta] /: \[Eta][\[Mu]_ia, \[Nu]_ia]^2 := d
\[Eta] /: \[Eta][\[Mu]_id, \[Mu]_id]   := p
\[Eta] /: \[Eta][\[Mu]_id, \[Nu]_id]^2 := p
\[Eta] /: \[Eta][\[Mu]_io, \[Mu]_io]   := d-p
\[Eta] /: \[Eta][\[Mu]_io, \[Nu]_io]^2 := d-p
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] \[Eta][\[Nu]_ia, \[Rho]_] := \[Eta][\[Mu], \[Rho]]
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] der[f_, x[i_][\[Nu]_ia]] := der[f, x[i][\[Mu]]]


Clear[x]
x /: x[i_][\[Mu]_ia]^2 := dota[x[i], x[i]]
x /: x[i_][\[Mu]_io]^2 := doto[x[i], x[i]]
x /: x[i_][\[Mu]_id]^2 := dota[x[i], x[i]] - doto[x[i], x[i]]
x /: x[i_][\[Mu]_ia] x[j_][\[Mu]_ia] := dota[x[i], x[j]]
x /: x[i_][\[Mu]_io] x[j_][\[Mu]_io] := doto[x[i], x[j]]
x /: x[i_][\[Mu]_id] x[j_][\[Mu]_id] := dota[x[i], x[j]] - doto[x[i], x[j]]
x /: \[Eta][\[Mu]_,   \[Nu]_ia] x[i_][\[Nu]_ia] := x[i][\[Mu]]
x /: \[Eta][\[Mu]_id, \[Nu]_id] x[i_][\[Nu]_id] := x[i][\[Mu]]
x /: \[Eta][\[Mu]_io, \[Nu]_io] x[i_][\[Nu]_io] := x[i][\[Mu]]


(* ::Text:: *)
(*Check that the objects are invariant  under our differential operators*)


checkInv[{\[Mu]_, \[Nu]_}, {i__}, inv_] := {
	\[ScriptCapitalD]d[1, 2][inv],
	\[ScriptCapitalP]d[\[Mu]][1, 2][inv],
	\[ScriptCapitalK]d[\[Mu]][1, 2][inv],
	\[ScriptCapitalM]d[\[Mu], \[Nu]][1, 2][inv]
};

pref = twoPtFun\[Xi]\[Eta] / f[\[Xi], \[Eta]];
Table[checkInv[{get$id, get$id}, {1, 2}, inv], {inv, {\[Xi]v, \[Chi]v, \[Eta]v}}] /. \[CapitalDelta][_] :> 0 // Together
checkInv[{get$id, get$id}, {1, 2}, pref] // Expand
checkInv[{get$id, get$id}, {1}, \[Eta]v] /. \[CapitalDelta][_] :> 0 // Expand
\[ScriptCapitalM]d[get$io, get$io][1][\[Chi]v] // Expand


(* ::Subsubsection::Closed:: *)
(*Defect channel*)


\[ScriptCapitalC]2defL2[i__][expr_] := With[{\[Mu] = get$id, \[Nu] = get$id}, 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	- 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];
\[ScriptCapitalC]2defS2[i__][expr_] := With[{\[Mu] = get$io, \[Nu] = get$io}, 
	- 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];
restore\[Chi]\[Eta] = Solve[{\[Chi]v == \[Chi], \[Eta]v == \[Eta]}, {dota[x[1], x[1]], doto[x[1], x[2]]}] // First;


L2block[\[CapitalDelta]_, p_][\[Chi]_] := \[Chi]^(-\[CapitalDelta]) Hypergeometric2F1[(\[CapitalDelta]+1)/2, \[CapitalDelta]/2, \[CapitalDelta]+1-p/2, 4/\[Chi]^2]
diffEq = (
	Expand[f[\[Chi], \[Eta]] (\[ScriptCapitalC]2defL2[1][twoPtFun\[Chi]\[Eta]] / twoPtFun\[Chi]\[Eta] - \[CapitalDelta](\[CapitalDelta] - p))] 
		/. restore\[Chi]\[Eta]
		// Collect[#, f_[\[Chi], \[Eta]], Simplify] &
)
diffEq /. f -> (L2block[\[CapitalDelta], p][#1] &) // Series[#, {\[Chi], Infinity, 20}] &


S2block[s_, q_][\[Eta]_] := Hypergeometric2F1[(q+s-2)/2, -s/2, (q-1)/2, 1-\[Eta]^2]
diffEq = (
	Expand[f[\[Chi], \[Eta]] (\[ScriptCapitalC]2defS2[1][twoPtFun\[Chi]\[Eta]] / twoPtFun\[Chi]\[Eta] - s(s + q - 2))] 
		/. restore\[Chi]\[Eta] 
		/. p -> d-q
		// Collect[#, f_[\[Chi], \[Eta]], Simplify] &
)
diffEq /. f -> (S2block[s, q][#2] &) // Series[#, {\[Eta], 1, 20}] &


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


Clear[\[ScriptCapitalC]2bulk]
\[ScriptCapitalC]2bulk[i__][expr_] := With[{\[Mu] = get$ia, \[Nu] = get$ia}, 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	- 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];
restore\[Xi]\[Eta] = Solve[{\[Xi]v == \[Xi], \[Eta]v == \[Eta]}, {dota[x[1], x[1]], doto[x[1], x[2]]}] // First;


diffEq = (
	Expand[\[Xi]^((\[CapitalDelta][1]+\[CapitalDelta][2])/2) f[\[Xi], \[Eta]] (\[ScriptCapitalC]2bulk[1, 2][twoPtFun\[Xi]\[Eta]] / twoPtFun\[Xi]\[Eta] - cas)] 
		/. restore\[Xi]\[Eta]
		/. f :> (#1^(-(\[CapitalDelta][1]+\[CapitalDelta][2])/2) f[#1, #2] &)
		// Collect[#, f_[\[Xi], \[Eta]], Simplify] &
)


(* ::Text:: *)
(*Compare with notes (same as Billo and friends)*)


(
	+ \[Xi]^2 (2 \[Eta]^2 + \[Xi] \[Eta] + 2) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi], \[Eta]]
	+ (1 - \[Eta]^2) (2 (1-\[Eta]^2) - \[Xi] \[Eta]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi], \[Eta]]
	- 2 \[Xi] (1 - \[Eta]^2) (2 \[Eta] + \[Xi]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi], \[Eta]]
	+ \[Xi] (2 (\[Eta]^2 + 1) - (2d - \[Xi] \[Eta])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi], \[Eta]]
	+ (\[Xi] (q - 2 + \[Eta]^2) - 2 \[Eta] (1 - \[Eta]^2)) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi], \[Eta]]
	- (cas + 1/4 (\[CapitalDelta][1]-\[CapitalDelta][2])^2 (2\[Eta]^2 + \[Xi] \[Eta] -2)) f[\[Xi], \[Eta]]
) - diffEq /. d -> p + q // Collect[#, f_[\[Xi], \[Eta]], Simplify] &


(* ::Text:: *)
(*Compare with D&O differential equation*)


(diffEq 
	/. f -> (f[- #1(#2 - I Sqrt[1-#2^2]), (#2 - I Sqrt[1-#2^2])^2] &) 
	/. {\[Xi] -> - u / Sqrt[v], \[Eta] -> (1+v) / (2Sqrt[v])} 
	/. {\[CapitalDelta][_] -> \[CapitalDelta]p, p -> d-2}
	 // Simplify[#, {u>0, v>1}] &
) // Collect[#, f_[u, v], Simplify] &
rhs = (
	+ 2((1-v)^2-u(1+v)) D[v D[f[u, v], v], v] 
	+ 2(1-u+v) u D[u D[f[u, v], u], u]
	- 4(1+u-v) u v D[f[u, v], u, v]
	- 2 d u D[f[u, v], u]
	- cas f[u, v]
) // Collect[#, f_[u, v], Simplify] &
%% - % // Expand


(* ::Subsubsection:: *)
(*Defect channel with U(1) twist*)


(* ::Text:: *)
(*We consider that 1, 2 are the orthogonal directions (we have codimension 2)*)


Expand[f[\[Chi], \[Eta]] \[ScriptCapitalM]d[1, 2][1][twoPtFun\[Chi]\[Eta]] / twoPtFun\[Chi]\[Eta]] //. {
	\[Eta][i_, j_io] x[a_][j_io] /; i==1 || i==2 :> x[a][i]
} // Simplify[#, doto[__] > 0] &


(* ::Text:: *)
(*We assume kinematics  Subscript[x, 1]^2 Subscript[x, 2]^1 > Subscript[x, 1]^1 Subscript[x, 2]^2*)


\[Eta]V = \[Eta]v /. doto[a_, b_] :> Sum[a[i] b[i], {i, 2}];
Sqrt[1 - \[Eta]V^2] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi],\[Eta]] // Simplify[#, x[1][2] x[2][1] > x[1][1] x[2][2]] &


(* ::Subsection::Closed:: *)
(*Line in d=3*)


(* ::Subsubsection:: *)
(*Defect channel*)


evalDot = {
	dota[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 3}],
	doto[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 2}]
};
{\[Chi]V, \[Eta]V} = {\[Chi]v, \[Eta]v} /. evalDot;
eval\[Chi]\[Eta] = {\[Chi] -> \[Chi]V, \[Eta] -> \[Eta]V};
restoreInv = Solve[{
	\[Chi]V == \[Chi], \[Eta]V == \[Eta], 
	x[1][1] == 1, x[1][2] == 0, x[1][3] == 0,
	(* x[2][1] \[Equal] x1, x[2][2] \[Equal] x2, *) x[2][3] == 0},
	{x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]}] // First // FullSimplify[#, {0<\[Eta], \[Eta]<1, \[Chi]>4}] &


{\[Chi]V, \[Eta]V} /. restoreInv // Simplify[#, 1>\[Eta]>0&&\[Chi]>2] &
%/.(-2+\[Chi]^2+\[Chi] Sqrt[-4+\[Chi]^2])^a_:>((\[Chi]+Sqrt[-4+\[Chi]^2])/Sqrt[2])^(2a)


twoPtFunEval


expr /. \[Chi]V->\[Chi] /. \[Eta]V->\[Eta] // Expand


I(
	x[1][1] D[\[Eta]V, x[1][2]] - 
	x[1][2] D[\[Eta]V, x[1][1]]
) // Expand


twoPtFunEval


twoPtFunEval = twoPtFun\[Chi]\[Eta] /. evalDot /. eval\[Chi]\[Eta];
expr = (
	I(x[1][1] d[1][2] - x[1][2] d[1][1])
) /. {d[i_][\[Mu]_] :> f[\[Chi],\[Eta]] D[twoPtFunEval, x[i][\[Mu]]] / twoPtFunEval};
expr /. restoreInv // Simplify[#, \[Eta]>\[Chi]>0] &
% /. (-2+\[Chi]^2+\[Chi] Sqrt[-4+\[Chi]^2])^a_:>((\[Chi]+Sqrt[-4+\[Chi]^2])/Sqrt[2])^(2a) // Simplify[#, \[Eta]>\[Chi]>0] &
quo = Expand[expr] / (I Sqrt[1-\[Eta]V^2] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi]V, \[Eta]V]);
quo /. {\[Chi]->\[Chi]V, \[Eta]->\[Eta]V} /. randRules[x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]] // Expand


KK[\[Mu]_][i_][expr_] := -(
	+ Sum[x[i][\[Nu]]^2, {\[Nu], 3}] D[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] Sum[x[i][\[Nu]] D[expr, x[i][\[Nu]]], {\[Nu], 3}]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
);
DD[\[Mu]_][i_][expr_] := (
	+ Sum[x[i][\[Nu]] D[expr, x[i][\[Nu]]], {\[Nu], 3}]
	+ \[CapitalDelta][i] expr
);


xorth2 = x[1][1]^2 + x[1][2]^2;
xpar3 = x[1][3] - x[2][3];
twoPt = xpar3^(-\[CapitalDelta][1]-\[CapitalDelta][2]) f[xorth2 / (xpar3)^2];
f[xorth2 / (xpar3)^2] (KK[3][1][twoPt] + KK[3][2][twoPt]) / twoPt // Expand;
% / xp3 /. {x[1][3] -> xp3 + x[2][3],  x[1][1] -> Sqrt[xo2 - x[1][2]^2], x[2][1|2] -> 0} // Expand
% /. xo2 -> xx xp3^2



int1 = Exp[Integrate[(\[Eta]+r Sqrt[\[Eta]^2-1])/(\[Eta]^2-1),\[Eta]]]
Integrate[int1 /. r -> 1, \[Eta]]
Integrate[int1 /. r -> 2, \[Eta]]
Integrate[int1 /. r -> 3, \[Eta]]
Integrate[int1 /. r -> 1/2, \[Eta]]


DSolve[f[xx] \[CapitalDelta][1]+xx f[xx] \[CapitalDelta][1]-f[xx] \[CapitalDelta][2]+xx f[xx] \[CapitalDelta][2]+2 xx Derivative[1][f][xx]+2 xx^2 Derivative[1][f][xx]==0, f[xx], xx] // Simplify


xp3^(-\[CapitalDelta][1]-\[CapitalDelta][2]) xx^(1/2 (-\[CapitalDelta][1]+\[CapitalDelta][2])) (1+xx)^-\[CapitalDelta][2] /. xx -> xo2 / xp3^2 // Simplify[#, xo2>xp3>0] &


Kx[i_][\[Mu]_] := (
	( x[i][\[Mu]] - a[\[Mu]] dota[x[i], x[i]] ) /
	( 1 - 2 dota[a, x[i]] + dota[a, a] dota[x[i], x[i]] )
) /. evalDot;


sol = Solve[((Kx[1][3]-Kx[2][3]) /. a[1|2] :> 0 /. evalDot) == 0, a[3]] // First


Kx[1][3] /. a[1|2] :> 0 /. sol // Together // Simplify
Kx[2][3] /. a[1|2] :> 0 /. sol // Together // Simplify


Kx[1][3] /. a[1|2] :> 0 /. a[3] -> x[1][3]/dota[x[1], x[1]] /. evalDot // Together
Kx[2][3] /. a[1|2] :> 0 /. a[3] -> x[1][3]/dota[x[1], x[1]] /. evalDot /. x[2][3] -> 0 // Together


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	- \[Xi] f'[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	-d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	2 d == c,
	(-(1/2)-2 d) == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


diffEqf /. f -> (#^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-1/2, 2\[CapitalDelta], -1/#] &) // FullSimplify


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 2}], d -> 2};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][2])^(-\[CapitalDelta][1]) (2 x[2][2])^(-\[CapitalDelta][2]);


expr = (1/x[2][2] (I d[1][1] x[1][0] x[1][2]+d[1][1] x[1][1] x[1][2]-I d[1][1] x[1][2] x[2][0]
-d[1][1] x[1][2] x[2][1]-I d[1][1] x[1][0] x[2][2]+d[1][1] x[1][1] x[2][2]-d[2][2] x[1][2] x[2][2]
+I d[1][1] x[2][0] x[2][2]-d[1][1] x[2][1] x[2][2]+d[2][2] x[2][2]^2
-d[1][2] (x[1][0]^2+x[1][1]^2-2 x[1][0] x[2][0]
+x[2][0]^2-2 x[1][1] x[2][1]+x[2][1]^2-x[1][2] x[2][2]
+x[2][2]^2)+d[1][0] (-x[1][2] x[2][0]+I x[1][2] x[2][1]-I x[1][1] (x[1][2]-x[2][2])
-x[2][0] x[2][2]
-I x[2][1] x[2][2]+x[1][0] (x[1][2]+x[2][2])))
+ 4 \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (\[Xi]+1) f''[\[Xi]]
	+ 2 \[Xi] (4 \[CapitalDelta]p (\[Xi] + 1) + 2 \[Xi] - 1) f'[\[Xi]]
	+ ( 2\[CapitalDelta]p(2\[CapitalDelta]p(\[Xi]+1) - 3) - \[CapitalDelta](\[CapitalDelta]-3)) f[\[Xi]]
	+ 4 \[Xi] (\[Xi] + 1) f'[\[Xi]] + 4 \[CapitalDelta]p (\[Xi] + 1) f[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsection:: *)
(*\[ScriptCapitalN]=2 line in d=3*)


(* ::Subsubsection::Closed:: *)
(*Defect channel*)


evalDot = {
	dota[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 3}],
	doto[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 2}]
};
{\[Chi]V, \[Eta]V} = {\[Chi]v, \[Eta]v} /. evalDot;
eval\[Chi]\[Eta] = {\[Chi] -> \[Chi]V, \[Eta] -> \[Eta]V};
restoreInv = Solve[{
	\[Chi]V == \[Chi], \[Eta]V == \[Eta], 
	x[1][1] == 1, x[1][2] == 0, x[1][3] == 0,
	(* x[2][1] \[Equal] x1, x[2][2] \[Equal] x2, *) x[2][3] == 0},
	{x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]}] // First // FullSimplify[#, {0<\[Eta], \[Eta]<1, \[Chi]>4}] &


{\[Chi]V, \[Eta]V} /. restoreInv // Simplify[#, 1>\[Eta]>0&&\[Chi]>2] &
%/.(-2+\[Chi]^2+\[Chi] Sqrt[-4+\[Chi]^2])^a_:>((\[Chi]+Sqrt[-4+\[Chi]^2])/Sqrt[2])^(2a)


twoPtFunEval


expr /. \[Chi]V->\[Chi] /. \[Eta]V->\[Eta] // Expand


I(
	x[1][1] D[\[Eta]V, x[1][2]] - 
	x[1][2] D[\[Eta]V, x[1][1]]
) // Expand


twoPtFunEval = twoPtFun\[Chi]\[Eta] /. evalDot /. eval\[Chi]\[Eta];
expr = (
	I(x[1][1] d[1][2] - x[1][2] d[1][1])
) /. {d[i_][\[Mu]_] :> f[\[Chi],\[Eta]] D[twoPtFunEval, x[i][\[Mu]]] / twoPtFunEval};
expr /. restoreInv // Simplify[#, \[Eta]>\[Chi]>0] &
% /. (-2+\[Chi]^2+\[Chi] Sqrt[-4+\[Chi]^2])^a_:>((\[Chi]+Sqrt[-4+\[Chi]^2])/Sqrt[2])^(2a) // Simplify[#, \[Eta]>\[Chi]>0] &
quo = Expand[expr] / (I Sqrt[1-\[Eta]V^2] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi]V, \[Eta]V]);
quo /. {\[Chi]->\[Chi]V, \[Eta]->\[Eta]V} /. randRules[x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]] // Expand


Kx[i_][\[Mu]_] := (
	( x[i][\[Mu]] - a[\[Mu]] dota[x[i], x[i]] ) /
	( 1 - 2 dota[a, x[i]] + dota[a, a] dota[x[i], x[i]] )
) /. evalDot;


sol = Solve[((Kx[1][3]-Kx[2][3]) /. a[1|2] :> 0 /. evalDot) == 0, a[3]] // First


Kx[1][3] /. a[1|2] :> 0 /. sol // Together // Simplify
Kx[2][3] /. a[1|2] :> 0 /. sol // Together // Simplify


Kx[1][3] /. a[1|2] :> 0 /. a[3] -> x[1][3]/dota[x[1], x[1]] /. evalDot // Together
Kx[2][3] /. a[1|2] :> 0 /. a[3] -> x[1][3]/dota[x[1], x[1]] /. evalDot /. x[2][3] -> 0 // Together


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	- \[Xi] f'[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	-d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	2 d == c,
	(-(1/2)-2 d) == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


diffEqf /. f -> (#^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-1/2, 2\[CapitalDelta], -1/#] &) // FullSimplify


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 2}], d -> 2};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][2])^(-\[CapitalDelta][1]) (2 x[2][2])^(-\[CapitalDelta][2]);


expr = (1/x[2][2] (I d[1][1] x[1][0] x[1][2]+d[1][1] x[1][1] x[1][2]-I d[1][1] x[1][2] x[2][0]
-d[1][1] x[1][2] x[2][1]-I d[1][1] x[1][0] x[2][2]+d[1][1] x[1][1] x[2][2]-d[2][2] x[1][2] x[2][2]
+I d[1][1] x[2][0] x[2][2]-d[1][1] x[2][1] x[2][2]+d[2][2] x[2][2]^2
-d[1][2] (x[1][0]^2+x[1][1]^2-2 x[1][0] x[2][0]
+x[2][0]^2-2 x[1][1] x[2][1]+x[2][1]^2-x[1][2] x[2][2]
+x[2][2]^2)+d[1][0] (-x[1][2] x[2][0]+I x[1][2] x[2][1]-I x[1][1] (x[1][2]-x[2][2])
-x[2][0] x[2][2]
-I x[2][1] x[2][2]+x[1][0] (x[1][2]+x[2][2])))
+ 4 \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (\[Xi]+1) f''[\[Xi]]
	+ 2 \[Xi] (4 \[CapitalDelta]p (\[Xi] + 1) + 2 \[Xi] - 1) f'[\[Xi]]
	+ ( 2\[CapitalDelta]p(2\[CapitalDelta]p(\[Xi]+1) - 3) - \[CapitalDelta](\[CapitalDelta]-3)) f[\[Xi]]
	+ 4 \[Xi] (\[Xi] + 1) f'[\[Xi]] + 4 \[CapitalDelta]p (\[Xi] + 1) f[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsection:: *)
(*(1,1) boundary in d=3*)


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


expr = (1/(x[1][2]+x[2][2]) (
	+2 I d[1][1] x[1][0] x[1][2]
	+4 d[1][1] x[1][1] x[1][2]
	+4 d[1][2] x[1][2]^2
	-2 I d[1][1] x[1][2] x[2][0]
	-4 d[1][1] x[1][2] x[2][1]
	-2 I d[1][1] x[1][0] x[2][2]
	-4 d[1][2] x[1][2] x[2][2]
	+2 I d[1][1] x[2][0] x[2][2]
	+d[1][0] (
		4 x[1][0] x[1][2]-2 I (x[1][2] (-2 I x[2][0]-x[2][1])
		+x[1][1] (x[1][2]-x[2][2])+x[2][1] x[2][2])
	)
	+4 \[CapitalDelta]p (x[1][2]-x[2][2]) pref f[inv]
)
	+ 4 \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (\[Xi]+1) f''[\[Xi]]
	+ 2 \[Xi] (4 \[CapitalDelta]p (\[Xi] + 1) + 2 \[Xi] - 1) f'[\[Xi]]
	+ ( 2\[CapitalDelta]p(2\[CapitalDelta]p(\[Xi]+1) - 3) - \[CapitalDelta](\[CapitalDelta]-3)) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] Derivative[1][f][\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	+ (-1/2 r^2 + r) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- (1/2(1/2-1) - 1/2(r-1)^2) f[\[Xi]]
) // Collect[#, G_[\[Xi]], Factor] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	3/4-2 d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	-1+2 d == c,
	-(1/2)-2 d == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


(* ::Subsection:: *)
(*OSp(1|4) boundary in d=4*)


(* ::Subsubsection::Closed:: *)
(*General*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 3}], d -> 3};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][3])^(-\[CapitalDelta][1]) (2 x[2][3])^(-\[CapitalDelta][2]);


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


expr = (
(2 (x[1][0]^2 \[ScriptD][1][0]+x[1][3]^2 \[ScriptD][1][0]-I x[1][1] x[2][0] \[ScriptD][1][0]+x[2][0]^2 \[ScriptD][1][0]
+I x[2][0] x[2][1] \[ScriptD][1][0]+I x[1][3] x[2][2] \[ScriptD][1][0]-2 x[1][3] x[2][3] \[ScriptD][1][0]
-I x[2][2] x[2][3] \[ScriptD][1][0]+x[2][3]^2 \[ScriptD][1][0]+I x[1][1]^2 \[ScriptD][1][1]+I x[1][3]^2 \[ScriptD][1][1]
-x[1][1] x[2][0] \[ScriptD][1][1]-2 I x[1][1] x[2][1] \[ScriptD][1][1]+x[2][0] x[2][1] \[ScriptD][1][1]
+I x[2][1]^2 \[ScriptD][1][1]-x[1][3] x[2][2] \[ScriptD][1][1]-2 I x[1][3] x[2][3] \[ScriptD][1][1]+x[2][2] x[2][3] \[ScriptD][1][1]
+I x[2][3]^2 \[ScriptD][1][1]-x[1][1] x[1][3] \[ScriptD][1][2]-I x[1][3] x[2][0] \[ScriptD][1][2]+x[1][3] x[2][1] \[ScriptD][1][2]
-I x[1][1] x[2][2] \[ScriptD][1][2]+x[2][0] x[2][2] \[ScriptD][1][2]+I x[2][1] x[2][2] \[ScriptD][1][2]+x[1][1] x[2][3] \[ScriptD][1][2]
+I x[2][0] x[2][3] \[ScriptD][1][2]-x[2][1] x[2][3] \[ScriptD][1][2]+x[1][0] (-2 x[2][0] \[ScriptD][1][0]-I x[2][1] \[ScriptD][1][0]
-x[2][1] \[ScriptD][1][1]+x[1][1] (I \[ScriptD][1][0]+\[ScriptD][1][1])+x[1][2] \[ScriptD][1][2]+I x[1][3] \[ScriptD][1][2]-x[2][2] \[ScriptD][1][2]
-I x[2][3] \[ScriptD][1][2])+x[1][2] (x[1][3] (-I \[ScriptD][1][0]+\[ScriptD][1][1])+I (x[2][3] (\[ScriptD][1][0]+I \[ScriptD][1][1])+(x[1][1]
+I x[2][0]-x[2][1]) \[ScriptD][1][2]))))/(x[1][0]+I (x[1][1]+I x[2][0]-x[2][1]))
+ 4 \[CapitalDelta]p id
) /. {
	\[ScriptD][i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]],
	id :> pref f[inv]
};
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ 4 \[Xi]^2 (1+\[Xi]) f''[\[Xi]]
	+ 4 \[Xi] (-1+\[Xi]+2 \[CapitalDelta]p (1+\[Xi])) f'[\[Xi]]
	+ (4 \[CapitalDelta]-\[CapitalDelta]^2+4 \[CapitalDelta]p (-2+\[CapitalDelta]p+\[CapitalDelta]p \[Xi])) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] f'[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


expr = (id \[CapitalDelta]p-(x[1][3] (-I x[1][2] \[ScriptD][1][0]
+x[1][3] \[ScriptD][1][0]+I x[2][2] \[ScriptD][1][0]-x[2][3] \[ScriptD][1][0]+x[1][2] \[ScriptD][1][1]
+I x[1][3] \[ScriptD][1][1]-x[2][2] \[ScriptD][1][1]-I x[2][3] \[ScriptD][1][1]+I x[1][0] \[ScriptD][1][2]
-x[1][1] \[ScriptD][1][2]-I x[2][0] \[ScriptD][1][2]+x[2][1] \[ScriptD][1][2]-x[1][0] \[ScriptD][1][3]
-I x[1][1] \[ScriptD][1][3]+x[2][0] \[ScriptD][1][3]+I x[2][1] \[ScriptD][1][3]))/(x[1][0]
+I x[1][1]-x[2][0]-I x[2][1])
) /. {
	\[ScriptD][i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]],
	id :> pref f[inv]
};
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- (1/2(1/2-1) - 1/2(r-1)^2) f[\[Xi]]
) // Collect[#, G_[\[Xi]], Factor] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	3/4-2 d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	-1+2 d == c,
	-(1/2)-2 d == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


(* ::Subsection:: *)
(*Accross dimensions*)


(* ::Subsubsection::Closed:: *)
(*Bulk channel*)


bulkBlock[\[CapitalDelta]_, \[CapitalDelta]1_, \[CapitalDelta]2_, d_][\[Xi]_] :=(
	\[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[(\[CapitalDelta]+\[CapitalDelta]1-\[CapitalDelta]2)/2, (\[CapitalDelta]-\[CapitalDelta]1+\[CapitalDelta]2)/2, \[CapitalDelta]+1-d/2, -\[Xi]]
);
bulkSusyBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2, \[CapitalDelta]/2, \[CapitalDelta]+2-d/2, -\[Xi]]


diffEqf = (
	+ 4 \[Xi]^2 (1+\[Xi]) f''[\[Xi]]
	+ (-2 d \[Xi]+4 (1+2 \[CapitalDelta]p) \[Xi] (1+\[Xi])) f'[\[Xi]]
	+ (-\[CapitalDelta]^2+d (\[CapitalDelta]-2 \[CapitalDelta]p)+4 \[CapitalDelta]p^2 (1+\[Xi])) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] f'[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG /. G -> bulkSusyBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], \[Xi], d]
(* DSolve[diffEqG == 0, G[\[Xi]], \[Xi]] *)


diff = (
	+ bulkSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		+ bulkBlock[\[CapitalDelta], 0, 0, d][\[Xi]]
		+ \[CapitalDelta]^2 / ( (2\[CapitalDelta] - d + 2) (2\[CapitalDelta] - d + 4) ) bulkBlock[\[CapitalDelta]+2, 0, 0, d][\[Xi]]
	)
) /. randRules[\[CapitalDelta], d, \[Xi]]


(* ::Subsubsection::Closed:: *)
(*Boundary channel*)


defectBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], (2-d+2 \[CapitalDelta])/2, 2\[CapitalDelta]-d+2, -1/\[Xi]];
defectSusyBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], (2-d+2 \[CapitalDelta])/2, 2\[CapitalDelta]-d+3, -1/\[Xi]];


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) Derivative[1][f][\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
) /. f -> defectBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], d, \[Xi]]


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) Derivative[1][f][\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
	- \[CapitalDelta] f[\[Xi]]
	- \[Xi] f'[\[Xi]]
) /. f -> defectSusyBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], d, \[Xi]]


diff = (
	+ defectSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		defectBlock[\[CapitalDelta], d][\[Xi]]
		+ \[CapitalDelta] / (4\[CapitalDelta] - 2d + 6) defectBlock[\[CapitalDelta]+1, d][\[Xi]]
	)
) /. randRules[\[CapitalDelta], d, \[Xi]]


(* ::Text:: *)
(*Code to find the solutions*)


(* diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ d/2 (1+2 \[Xi]) (f^\[Prime])[\[Xi]]
	- \[CapitalDelta] (1-d+\[CapitalDelta]) f[\[Xi]]
) // Collect[#, f_[\[Xi]], Factor] &
(z^(-e-1) diffEqf /. f -> ((-1/#)^e ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &
sol = Solve[{
	(e-\[CapitalDelta]) (1-d+e+\[CapitalDelta]) == 0,
	1/2 e (d-2 (1+e)) == - a b,
	2-d+2 e == c,
	1/2 (d-4 (1+e))  == -(a + b + 1)
}, {a, b, c, e}];
\[Xi]^(-e) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates *)
