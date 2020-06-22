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
(*Differential Operator Bobev*)


(* ::Subsection:: *)
(*Compute blocks*)


Clear[\[Eta]]
SetAttributes[\[Eta], Orderless]
\[Eta] /: \[Eta][\[Mu]_, \[Mu]_] := d
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_]^2 := d
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_] \[Eta][\[Nu]_, \[Rho]_] := \[Eta][\[Mu], \[Rho]]
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_] der[f_, x[i_][\[Nu]_]] := der[f, x[i][\[Mu]]]


Clear[dot, x2];
SetAttributes[dot, Orderless];
SetAttributes[x2, Orderless];
x /: x[i_][\[Mu]_]^2 := dot[x[i], x[i]]
x /: x[i_][\[Mu]_] x[j_][\[Mu]_] := dot[x[i], x[j]]
x /: \[Eta][\[Mu]_, \[Nu]_] x[i_][\[Nu]_] := x[i][\[Mu]]


Clear[\[Delta], dot, x2, Uv, Vv];
\[Delta] = KroneckerDelta;
x2v[i_, j_] := dot[x[i], x[i]] - 2 dot[x[i], x[j]] + dot[x[j], x[j]];
restoreX2 = dot[x[i_], x[j_]] /; i != j :> -1/2(x2[i, j] - dot[x[i], x[i]] - dot[x[j], x[j]]);
Uv = x2[1, 2] x2[3, 4] / (x2[1, 3] x2[2, 4]);
Vv = x2[1, 4] x2[2, 3] / (x2[1, 3] x2[2, 4]);
restoreUV = Solve[{Uv == u, Vv == v}, {x2[1, 2], x2[1, 4]}] // First;


uv2zzb = {u -> z zb, v -> (1-z) (1-zb)};
ztouv = Solve[{u == z zb, v == (1-z) (1-zb)}, {z, zb}] // First;
fun2zzb = Flatten @ Table[
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"i", ",", "j"}], ")"}],
Derivative],
MultilineFunction->None]\)[u,v]->(\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"i", ",", "j"}], ")"}],
Derivative],
MultilineFunction->None]\)[u,v] 
		/. f -> Function[{u, v}, f[1/2 (1+u-Sqrt[-4 u+(1+u-v)^2]-v),1/2 (1+u+Sqrt[-4 u+(1+u-v)^2]-v)]] 
		/. uv2zzb
	) // Simplify[#, zb > z] &
, {i, 0, 2}, {j, 0, 2}];


der[(\[CapitalDelta][_]|\[Eta][__]|d), x[_][_]] := 0
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Eta][\[Mu], \[Nu]]
der[dot[x[i_], x[j_]], x[k_][\[Mu]_]] := \[Delta][i, k] x[j][\[Mu]] + \[Delta][j, k] x[i][\[Mu]];
der[x2[i_, j_], x[k_][\[Mu]_]] := der[x2v[i, j], x[k][\[Mu]]];
der[f_[u, v], x[i_][\[Mu]_]] := (
	+ D[f[u, v], u] der[Uv, x[i][\[Mu]]]
	+ D[f[u, v], v] der[Vv, x[i][\[Mu]]]
);


\[ScriptCapitalD]d[i_][expr_] := With[{\[Mu] = Unique[]}, -I ( x[i][\[Mu]] der[expr, x[i][\[Mu]]] + \[CapitalDelta][i] expr )];
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := -I der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := With[{\[Nu] = Unique[]}, -I (
	+ dot[x[i], x[i]] der[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] x[i][\[Nu]] der[expr, x[i][\[Nu]]]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
)];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -I (
	+ x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


Clear[\[ScriptCapitalC]2d]
\[ScriptCapitalC]2d[i__][expr_] := With[{\[Mu] = Unique[], \[Nu] = Unique[]}, 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	+ 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	+ 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Nu], \[Mu]][i][expr]]
];


fourPtFun = (
	x2[1, 2]^(-(\[CapitalDelta][1]+\[CapitalDelta][2])/2) 
	x2[3, 4]^(-(\[CapitalDelta][3]+\[CapitalDelta][4])/2) 
	(x2[2, 4] / x2[1, 4])^((\[CapitalDelta][1]-\[CapitalDelta][2])/2) 
	(x2[1, 4] / x2[1, 3])^((\[CapitalDelta][3]-\[CapitalDelta][4])/2) 
	f[u, v]
);


expr = \[ScriptCapitalC]2d[1, 2][fourPtFun] / fourPtFun // ExpandAll;
expr = f[u,v] expr /. restoreX2 /. restoreUV // Together // Collect[#, f_[u, v], Simplify] &;
expr = expr /. fun2zzb /. uv2zzb // Simplify // Collect[#, f_[z, zb], Factor] & // FullSimplify


(* ::Text:: *)
(*Compare with Dolan & Osborn*)


exprDO = 2 (
	+ z^2  (1-z)  \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]
	+ zb^2 (1-zb) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]
	+ c( z \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb] + zb \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb] )
	- (a + b + 1) (z^2 \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb] + zb^2 \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb])
	- a b (z + zb) f[z,zb]
	+ (d-2) z zb / (z - zb) (
		(1-z)  \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb] -
		(1-zb) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]
	)
) /. {
	a -> -1/2(\[CapitalDelta][1] - \[CapitalDelta][2]),
	b -> +1/2(\[CapitalDelta][3] - \[CapitalDelta][4]),
	c -> 0
};
expr + exprDO // FullSimplify


With[{\[Mu] = Unique[]},
	expr = 2(
		+ (x[1][\[Mu]]-x[2][\[Mu]]) der[fourPtFun, x[1][\[Mu]]] 
		+ (\[CapitalDelta][1] + \[CapitalDelta][2]) fourPtFun
	) / fourPtFun // ExpandAll
];
expr = expr /. restoreX2 /. restoreUV // Together // Expand;
expr = f[u, v] (
	Limit[expr /. x2[a___, 4, b___] :> \[CapitalLambda], \[CapitalLambda] -> \[Infinity]]
	 /. {x2[1, 2] -> u x2[1, 3], x2[2, 3] -> v x2[1, 3]}
) // Expand;
expr /. fun2zzb /. uv2zzb // Simplify


k1d[\[Alpha]_, \[Beta]_, \[Gamma]_][x_] := x^(\[Alpha]/2) Hypergeometric2F1[(\[Alpha]-\[Beta])/2, (\[Alpha]+\[Gamma])/2, \[Alpha], x];
g2d[\[CapitalDelta]_, l_, \[CapitalDelta]12_, \[CapitalDelta]34_][z_, zb_] := 1 / (1 + KroneckerDelta[l, 0])(
	k1d[\[CapitalDelta]+l, \[CapitalDelta]12, \[CapitalDelta]34][z] k1d[\[CapitalDelta]-l, \[CapitalDelta]12, \[CapitalDelta]34][zb] + 
	k1d[\[CapitalDelta]+l, \[CapitalDelta]12, \[CapitalDelta]34][zb] k1d[\[CapitalDelta]-l, \[CapitalDelta]12, \[CapitalDelta]34][z]
);
g4d[\[CapitalDelta]_, l_, \[CapitalDelta]12_, \[CapitalDelta]34_][z_, zb_] := (z zb)/(z - zb) (
	k1d[\[CapitalDelta]+l, \[CapitalDelta]12, \[CapitalDelta]34][z]  k1d[\[CapitalDelta]-l-2, \[CapitalDelta]12, \[CapitalDelta]34][zb] - 
	k1d[\[CapitalDelta]+l, \[CapitalDelta]12, \[CapitalDelta]34][zb] k1d[\[CapitalDelta]-l-2, \[CapitalDelta]12, \[CapitalDelta]34][z]
);
k1d[\[CapitalDelta]_][z_] := k1d[\[CapitalDelta], 0, 0][z]
g4d[\[CapitalDelta]_, l_][z_, zb_] := g4d[\[CapitalDelta], l, 0, 0][z, zb]


diffEq = (
-(1/2) (z+zb) f[z,zb] (\[CapitalDelta][1]-\[CapitalDelta][2]) (\[CapitalDelta][3]-\[CapitalDelta][4])
+1/(z-zb) zb (z (-4-2 d (-1+zb)+zb (6-\[CapitalDelta][1]+\[CapitalDelta][2]+\[CapitalDelta][3]-\[CapitalDelta][4]))
+zb^2 (-2+\[CapitalDelta][1]-\[CapitalDelta][2]-\[CapitalDelta][3]+\[CapitalDelta][4])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]+2 (-1+zb) zb^2 \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]
+(z (-2 (-2+d) zb+z^2 (2-\[CapitalDelta][1]+\[CapitalDelta][2]+\[CapitalDelta][3]-\[CapitalDelta][4])+z zb (-6+2 d+\[CapitalDelta][1]-\[CapitalDelta][2]-\[CapitalDelta][3]+\[CapitalDelta][4])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb])/(z-zb)
+2 (-1+z) z^2 \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]
(* +(\[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2)) f[z, zb] *)
-(-(z+zb) f[z,zb] (\[CapitalDelta][3]-\[CapitalDelta][4])-2 (-1+zb) zb \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb]-2 (-1+z) z \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[z,zb])
+(\[CapitalDelta](\[CapitalDelta]-d+2) + l(l+d-2)) f[z, zb]
) /. {
	d -> 4,
	(* f \[Rule] Function[{z, zb}, g4d[\[CapitalDelta], l, \[CapitalDelta][1]-\[CapitalDelta][2], \[CapitalDelta][3]-\[CapitalDelta][4]][z, zb]] *)
	f -> Function[{z, zb}, z^(-1/2) zb^(-1/2) g4d[\[CapitalDelta]+1, l, \[CapitalDelta][1]-\[CapitalDelta][2]-1, \[CapitalDelta][3]-\[CapitalDelta][4]-1][z, zb]]
} // Together


diffEq /. {
	z -> RandomReal[WorkingPrecision->100],
	zb -> RandomReal[WorkingPrecision->100],
	l -> RandomReal[WorkingPrecision->100],
	\[CapitalDelta] -> RandomReal[WorkingPrecision->100],
	\[CapitalDelta][1] -> RandomReal[WorkingPrecision->100],
	\[CapitalDelta][2] -> RandomReal[WorkingPrecision->100],
	\[CapitalDelta][3] -> RandomReal[WorkingPrecision->100],
	\[CapitalDelta][4] -> RandomReal[WorkingPrecision->100]
} // Chop


g4d[\[CapitalDelta], l, \[CapitalDelta]12, \[CapitalDelta]12][z, zb]-g4d[\[CapitalDelta], l, -\[CapitalDelta]12, -\[CapitalDelta]12][z, zb]


(* ::Section:: *)
(*Bulk channel blocks*)


(* ::Subsection:: *)
(*Compute blocks*)


get$ia := ia[Unique[]]


SetAttributes[dot, Orderless];
x2[i_, j_] := dot[x[i], x[i]] - 2 dot[x[i], x[j]] + dot[x[j], x[j]];


der[(\[CapitalDelta][_]|\[Eta][__]|d), x[_][_]] := 0
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Eta][\[Mu], \[Nu]]
der[dot[x[i_], x[j_]], x[k_][\[Mu]_]] := \[Delta][i, k] x[j][\[Mu]] + \[Delta][j, k] x[i][\[Mu]];
der[f[\[Xi]], x[i_][\[Mu]_]] := f'[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];
der[f'[\[Xi]], x[i_][\[Mu]_]] := f''[\[Xi]] der[\[Xi]v, x[i][\[Mu]]];


\[ScriptCapitalD]d[i_][expr_] := With[{\[Mu] = get$ia}, -I ( x[i][\[Mu]] der[expr, x[i][\[Mu]]] + \[CapitalDelta][i] expr )];
\[ScriptCapitalP]d[\[Mu]_][i_][expr_] := -I der[expr, x[i][\[Mu]]];
\[ScriptCapitalK]d[\[Mu]_][i_][expr_] := With[{\[Nu] = get$ia}, -I (
	+ dot[x[i], x[i]] der[expr, x[i][\[Mu]]]
	- 2 x[i][\[Mu]] x[i][\[Nu]] der[expr, x[i][\[Nu]]]
	- 2 x[i][\[Mu]] \[CapitalDelta][i] expr
)];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] := -I (
	+ x[i][\[Mu]] der[expr, x[i][\[Nu]]] 
	- x[i][\[Nu]] der[expr, x[i][\[Mu]]]
);
\[ScriptCapitalD]d[i___][expr_] := Total[\[ScriptCapitalD]d[#][expr] & /@ {i}];
\[ScriptCapitalP]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalP]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalK]d[\[Mu]_][i___][expr_] := Total[\[ScriptCapitalK]d[\[Mu]][#][expr] & /@ {i}];
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i___][expr_] := Total[\[ScriptCapitalM]d[\[Mu], \[Nu]][#][expr] & /@ {i}];


\[Delta] = KroneckerDelta;


\[Xi]v = x2[1, 2] / (4 x[1][d] x[2][d]);
(* twoPtFunDef = (
	x[1][d] ^(-(\[CapitalDelta][1]-\[CapitalDelta][2])/2) 
	x[2][d] ^(+(\[CapitalDelta][1]-\[CapitalDelta][2])/2) 
	x2[1, 2]^(-(\[CapitalDelta][1]+\[CapitalDelta][2])/2) 
	G[\[Xi]]
); *)
twoPtFunDef = (
	(2 x[1][d])^(-\[CapitalDelta][1]) 
	(2 x[2][d])^(-\[CapitalDelta][2])
	f[\[Xi]]
);


Clear[\[Eta]]
SetAttributes[\[Eta], Orderless]
\[Eta] /: \[Eta][d, d] := 1
\[Eta] /: \[Eta][\[Mu]_ia, \[Mu]_ia] := d
\[Eta] /: \[Eta][\[Mu]_ia, \[Nu]_ia]^2 := d
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] \[Eta][\[Nu]_ia, \[Rho]_] := \[Eta][\[Mu], \[Rho]]
\[Eta] /: \[Eta][\[Mu]_, \[Nu]_ia] der[f_, x[i_][\[Nu]_ia]] := der[f, x[i][\[Mu]]]


x /: x[i_][\[Mu]_ia]^2 := dot[x[i], x[i]]
x /: x[i_][\[Mu]_ia] x[j_][\[Mu]_ia] := dot[x[i], x[j]]
x /: \[Eta][\[Mu]_, \[Nu]_ia] x[i_][\[Nu]_ia] := x[i][\[Mu]]


dummyFun = f;
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


simpIndx[expr_?NumericQ] := expr
simpIndx[expr_Plus] := Total[simpIndxPiece /@ List @@ expr]
simpIndxPiece[expr_] := Module[{
	idx = DeleteDuplicates @ Cases[expr, ia[_], Infinity],
	rule
},
	rule = Table[idx[[i]] -> ia[i], {i, Length@idx}];
	expr /. rule
]


CheckCommutator[\[ScriptCapitalD]d, \[ScriptCapitalP]d[\[Mu]], +I \[ScriptCapitalP]d[\[Mu]]] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalD]d, \[ScriptCapitalK]d[\[Mu]], -I \[ScriptCapitalK]d[\[Mu]]] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalM]d[\[Rho], \[Sigma]], +I(
	+ \[Eta][\[Mu], \[Rho]] \[ScriptCapitalM]d[\[Nu], \[Sigma]]
	- \[Eta][\[Nu], \[Rho]] \[ScriptCapitalM]d[\[Mu], \[Sigma]]
	- \[Eta][\[Mu], \[Sigma]] \[ScriptCapitalM]d[\[Nu], \[Rho]]
	+ \[Eta][\[Nu], \[Sigma]] \[ScriptCapitalM]d[\[Mu], \[Rho]]
)] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalP]d[\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalP]d[\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalP]d[\[Mu]])] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalM]d[\[Mu], \[Nu]], \[ScriptCapitalK]d[\[Rho]], I (\[Eta][\[Mu], \[Rho]] \[ScriptCapitalK]d[\[Nu]] - \[Eta][\[Nu], \[Rho]] \[ScriptCapitalK]d[\[Mu]])] // Expand // simpIndx


Clear[\[ScriptCapitalC]2d]
\[ScriptCapitalC]2d[i__][expr_] := With[{\[Mu] = get$ia, \[Nu] = get$ia}, 
	+ \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	+ 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	+ 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Nu], \[Mu]][i][expr]]
];


CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalP]d[\[Mu]], 0] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalK]d[\[Mu]], 0] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalM]d[\[Mu], \[Nu]], 0] // Expand // simpIndx


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-d);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2d[1, 2][twoPtFunDef] + \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = expr / (-4\[Xi]) /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Factor] &;
\[Xi]^(-(\[CapitalDelta]/2)+\[CapitalDelta][1]/2+\[CapitalDelta][2]/2) expr / (4\[Xi]) /. f -> (#^(-1/2(\[CapitalDelta][1]+\[CapitalDelta][2]-\[CapitalDelta])) g[#] &) // Collect[#, f_[\[Xi]], Factor] &


(* ::Text:: *)
(*Compare with Pedro's result in paper*)


\[Xi](1+\[Xi]) g''[\[Xi]] + (c + (a + b + 1) \[Xi]) g'[\[Xi]] + a b g[\[Xi]] /. {
	a -> 1 / 2 (\[CapitalDelta] + \[CapitalDelta][1] - \[CapitalDelta][2]),
	b -> 1 / 2 (\[CapitalDelta] - \[CapitalDelta][1] + \[CapitalDelta][2]),
	c -> \[CapitalDelta] - d/2 + 1
} // Collect[#, f_[\[Xi]], Factor] &


expr = (\[ScriptCapitalC]2d[1, 2][twoPtFunDef] + \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = expr /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Collect[#, \[Xi], Factor] &] &


\[ScriptCapitalC]ferm[expr_] := (
	- dot[x[1], x[1]] / x[1][d] der[expr, x[2][d]]
	+ dot[x[2], x[2]] / x[2][d] der[expr, x[1][d]]
);
expr = \[ScriptCapitalC]ferm[twoPtFunDef] / twoPtFunDef // ExpandAll;
expr = expr /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Collect[#, \[Xi], Factor] &] &


\[ScriptCapitalC]ferm[expr_] := (
	+ x[1][d] der[expr, x[2][d]]
	+ x[2][d] der[expr, x[1][d]]
);
expr = \[ScriptCapitalC]ferm[twoPtFunDef] / twoPtFunDef // ExpandAll;
expr = expr /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Collect[#, \[Xi], Factor] &] &


f[\[Xi]] der[twoPtFunDef, x[2][d]] / twoPtFunDef // ExpandAll
% /. restore\[Xi] // Together // Collect[#, f_[\[Xi]], Collect[#, \[Xi], Factor] &] &



