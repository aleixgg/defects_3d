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


(* ::Section::Closed:: *)
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
		- (x[1][\[Mu]]-x[2][\[Mu]]) der[fourPtFun, x[1][\[Mu]]] 
		+ (\[CapitalDelta][1] + \[CapitalDelta][2]) fourPtFun
	) / fourPtFun // ExpandAll
];
expr = expr /. restoreX2 /. restoreUV // Together // Expand;
expr = f[u, v] (
	Limit[expr /. x2[a___, 4, b___] :> \[CapitalLambda], \[CapitalLambda] -> \[Infinity]]
	 /. {x2[1, 2] -> u x2[1, 3], x2[2, 3] -> v x2[1, 3]}
) // Expand;
expr /. fun2zzb /. uv2zzb // Simplify


comm[A_, B_] := A.B-B.A
acomm[A_, B_] := A.B+B.A
lhs = acomm[a, b.c.d.e];
rhs = (
	+ acomm[a, b].c.d.e
	- b.comm[a, c].d.e
	- b.c.comm[a, d].e
	- b.c.d.comm[a, e]
);
lhs - rhs // TensorExpand


lhs = acomm[a, comm[b, c]];
rhs = (
	- acomm[b, comm[a, c]]
	+ comm[acomm[a, b], c]
);
lhs - rhs // TensorExpand // Collect[#, Dot[__], Factor] &


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
(* -(-(z+zb) f[z,zb] (\[CapitalDelta][3]-\[CapitalDelta][4])-2 (-1+zb) zb (f^(0,1))[z,zb]-2 (-1+z) z (f^(1,0))[z,zb]) *)
-(f[z,zb] (-4 \[CapitalDelta][2]-(z+zb) (\[CapitalDelta][3]-\[CapitalDelta][4]))-2 (-1+zb) zb \!\(\*SuperscriptBox[\(f\), 
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
	f -> Function[{z, zb}, z^(-1/2) zb^(-1/2) g4d[\[CapitalDelta]+1, l, 1+\[CapitalDelta][1]-\[CapitalDelta][2], 1+\[CapitalDelta][3]-\[CapitalDelta][4]][z, zb]]
} // Together


diffEq /. {
	z    -> RandomReal[WorkingPrecision->50],
	zb   -> RandomReal[WorkingPrecision->50],
	l    -> RandomReal[WorkingPrecision->50],
	\[CapitalDelta]    -> RandomReal[WorkingPrecision->50],
	\[CapitalDelta][1] -> RandomReal[WorkingPrecision->50],
	\[CapitalDelta][2] -> RandomReal[WorkingPrecision->50],
	\[CapitalDelta][3] -> RandomReal[WorkingPrecision->50],
	\[CapitalDelta][4] -> RandomReal[WorkingPrecision->50]
} // Chop


(* ::Section:: *)
(*Defect channel blocks*)


(* ::Subsection:: *)
(*Compute blocks*)


get$ia := ia[Unique[]]
get$id := id[Unique[]]


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


Clear[\[ScriptCapitalC]2def]
\[ScriptCapitalC]2def[i__][expr_] := With[{\[Mu] = get$id, \[Nu] = get$id}, 
	- \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	+ 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-d+1);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2def[1][twoPtFunDef] - \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = f[\[Xi]] expr /. restore\[Xi] // Collect[#, f_[\[Xi]], Factor] &


defBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-d/2+1, 2\[CapitalDelta]+2-d, -1/\[Xi]]
expr /. f -> defBlock[\[CapitalDelta], d] // FullSimplify


expr2 = 1/\[Chi] (-(1/\[Chi]))^\[CapitalDelta] expr /. f -> (#^(-\[CapitalDelta]) g[-1/#] &) /. \[Xi] -> -1/\[Chi] // Collect[#, g_[\[Chi]], Factor] &


DSolve[expr2 == 0, g[\[Chi]], \[Chi]]


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-1);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2def[1][twoPtFunDef] + (- \[ScriptCapitalC]val + \[CapitalDelta]p) twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = f[\[Xi]] expr /. restore\[Xi] /. d -> 3 // Collect[#, f_[\[Xi]], Factor] &


DSolve[expr == 0, f[\[Xi]], \[Xi]]


expr2 = 1/\[Chi] (-(1/\[Chi]))^(\[CapitalDelta]) expr /. f -> (#^(-\[CapitalDelta]) g[-1/#] &) /. \[Xi] -> -1/\[Chi] // Collect[#, g_[\[Chi]], Factor] &


Solve[4 a-2 a^2+2 \[CapitalDelta]-4 a \[CapitalDelta]-2 \[CapitalDelta]p==0,a] // FullSimplify


DSolve[expr2 == 0, g[\[Chi]], \[Chi]]


ansatz = {f -> (
	(* + defBlock[\[CapitalDelta]-1, 3][#] *)
	+ a[0] defBlock[\[CapitalDelta], 3][#]
	+ a[1] defBlock[\[CapitalDelta]+1/2, 3][#]
	+ a[2] defBlock[\[CapitalDelta]+2/2, 3][#]
	+ a[3] defBlock[\[CapitalDelta]+3/2, 3][#]
	+ a[4] defBlock[\[CapitalDelta]+4/2, 3][#]
&)};


expr /. ansatz // FullSimplify


Normal @ Series[%148, {\[Xi], 0, 4}]


Solve[ (2 \[CapitalDelta] a[0]+3 a[1]+4 a[2]-4 \[CapitalDelta] a[2])==0, a[2]]


(-2^(-4+2 \[CapitalDelta]) Sqrt[1/\[Xi]] \[Xi]^(3/2) (3 a[1]-12 a[3]+32 \[CapitalDelta] a[3])+\[Xi]^(7/2) ((105 2^(-10+2 \[CapitalDelta]) a[1])/Sqrt[1/\[Xi]]-(105 2^(-8+2 \[CapitalDelta]) a[3])/Sqrt[1/\[Xi]]+(35 2^(-5+2 \[CapitalDelta]) \[CapitalDelta] a[3])/Sqrt[1/\[Xi]])+\[Xi]^(5/2) (-((15 2^(-7+2 \[CapitalDelta]) a[1])/Sqrt[(1/\[Xi])])+(15 2^(-5+2 \[CapitalDelta]) a[3])/Sqrt[1/\[Xi]]-(5 2^(-2+2 \[CapitalDelta]) \[CapitalDelta] a[3])/Sqrt[1/\[Xi]])+\[Xi]^(3/2) ((9 2^(-6+2 \[CapitalDelta]) a[1])/Sqrt[1/\[Xi]]-(9 2^(-4+2 \[CapitalDelta]) a[3])/Sqrt[1/\[Xi]]+(3 2^(-1+2 \[CapitalDelta]) \[CapitalDelta] a[3])/Sqrt[1/\[Xi]])+2^(-3+2 \[CapitalDelta]) Sqrt[1/\[Xi]] Sqrt[\[Xi]] (3 a[1]+3 Sqrt[1/\[Xi]] a[1]-12 a[3]+32 \[CapitalDelta] a[3]+12 Sqrt[1/\[Xi]] a[3]-32 \[CapitalDelta] Sqrt[1/\[Xi]] a[3])+2^(-2+2 \[CapitalDelta]) Sqrt[1/\[Xi]] (\[CapitalDelta] a[0]+4 a[2]-4 \[CapitalDelta] a[2]-48 \[CapitalDelta] a[4])+\[Xi]^4 ((77 2^(-10+2 \[CapitalDelta]) \[CapitalDelta] a[0])/Sqrt[1/\[Xi]]-(63 2^(-8+2 \[CapitalDelta]) a[2])/Sqrt[1/\[Xi]]+(63 2^(-8+2 \[CapitalDelta]) \[CapitalDelta] a[2])/Sqrt[1/\[Xi]]-(231 2^(-6+2 \[CapitalDelta]) \[CapitalDelta] a[4])/Sqrt[1/\[Xi]])+\[Xi]^3 (-((45 2^(-9+2 \[CapitalDelta]) \[CapitalDelta] a[0])/Sqrt[(1/\[Xi])])+(35 2^(-7+2 \[CapitalDelta]) a[2])/Sqrt[1/\[Xi]]-(35 2^(-7+2 \[CapitalDelta]) \[CapitalDelta] a[2])/Sqrt[1/\[Xi]]+(135 2^(-5+2 \[CapitalDelta]) \[CapitalDelta] a[4])/Sqrt[1/\[Xi]])+\[Xi]^2 ((7 2^(-6+2 \[CapitalDelta]) \[CapitalDelta] a[0])/Sqrt[1/\[Xi]]-(5 2^(-4+2 \[CapitalDelta]) a[2])/Sqrt[1/\[Xi]]+(5 2^(-4+2 \[CapitalDelta]) \[CapitalDelta] a[2])/Sqrt[1/\[Xi]]-(21 2^(-2+2 \[CapitalDelta]) \[CapitalDelta] a[4])/Sqrt[1/\[Xi]])+\[Xi] (-((5 2^(-5+2 \[CapitalDelta]) \[CapitalDelta] a[0])/Sqrt[(1/\[Xi])])+(3 2^(-3+2 \[CapitalDelta]) a[2])/Sqrt[1/\[Xi]]-(3 2^(-3+2 \[CapitalDelta]) \[CapitalDelta] a[2])/Sqrt[1/\[Xi]]+(15 2^(-1+2 \[CapitalDelta]) \[CapitalDelta] a[4])/Sqrt[1/\[Xi]])+(2^(-3+2 \[CapitalDelta]) (3 \[CapitalDelta] a[0]+4 \[CapitalDelta] Sqrt[1/\[Xi]] a[0]-4 a[2]+4 \[CapitalDelta] a[2]-144 \[CapitalDelta] a[4]+192 \[CapitalDelta] Sqrt[1/\[Xi]] a[4]))/Sqrt[1/\[Xi]]
)/. (1/a_)^b_ :> a^(-b) // Expand // Collect[#, \[Xi], Factor] &;
% //. {
a[2]->(2 \[CapitalDelta] a[0]+3 a[1])/(4 (-1+\[CapitalDelta])),
a[3]->-((3 a[1])/(4 (-3+8 \[CapitalDelta]))),
a[4]->(\[CapitalDelta] a[0]+3 a[1]+4 a[2]-4 \[CapitalDelta] a[2])/(48 \[CapitalDelta])
}// Collect[#, \[Xi], Factor] &


diffEq = (
	(-1+\[CapitalDelta]) \[CapitalDelta] f[\[Xi]]-3/2 (1+2 \[Xi]) Derivative[1][f][\[Xi]]-\[Xi] (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]]
	+ \[CapitalDelta]p f[\[Xi]]
);
DSolve[diffEq == 0, f[\[Xi]], \[Xi]]


di


(* ::Section:: *)
(*Bulk channel blocks*)


(* ::Subsection::Closed:: *)
(*Compute blocks*)


get$ia := ia[Unique[]]


SetAttributes[dot, Orderless];
x2[i_, j_] := dot[x[i], x[i]] - 2 dot[x[i], x[j]] + dot[x[j], x[j]];


der[(\[CapitalDelta][_]|\[Eta][__]|d|\[CapitalDelta]p), x[_][_]] := 0
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
	- \[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]])
	+ 1/2 \[ScriptCapitalM]d[\[Mu], \[Nu]][i][\[ScriptCapitalM]d[\[Mu], \[Nu]][i][expr]]
];


CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalP]d[\[Mu]], 0] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalK]d[\[Mu]], 0] // Expand // simpIndx
CheckCommutator[\[ScriptCapitalC]2d, \[ScriptCapitalM]d[\[Mu], \[Nu]], 0] // Expand // simpIndx


\[ScriptCapitalC]val = +\[CapitalDelta] (\[CapitalDelta]-d);
restore\[Xi] = {dot[x[1], x[2]] -> 1 / 2 (dot[x[1], x[1]] + dot[x[2], x[2]] - 4 \[Xi] x[1][d] x[2][d])};
expr = (\[ScriptCapitalC]2d[1, 2][twoPtFunDef] - \[ScriptCapitalC]val twoPtFunDef) / twoPtFunDef // ExpandAll;
expr = expr /. restore\[Xi] // Together // Numerator // Collect[#, f_[\[Xi]], Simplify] &;


expr // Collect[#, f_[\[Xi]], Simplify] &
expr /. {d -> 3, \[CapitalDelta][_] -> \[CapitalDelta]p} // Collect[#, f_[\[Xi]], Simplify] &
expr /. {d -> 4, \[CapitalDelta][_] -> \[CapitalDelta]p} // Collect[#, f_[\[Xi]], Simplify] &
\[Xi]^(-(\[CapitalDelta]/2)+\[CapitalDelta][1]/2+\[CapitalDelta][2]/2) expr / (4\[Xi]) /. f -> (#^(-1/2(\[CapitalDelta][1]+\[CapitalDelta][2]-\[CapitalDelta])) g[#] &) // Collect[#, f_[\[Xi]], Factor] &


(* ::Text:: *)
(*Compare with Pedro's result in paper*)


\[Xi](1+\[Xi]) g''[\[Xi]] + (c + (a + b + 1) \[Xi]) g'[\[Xi]] + a b g[\[Xi]] /. {
	a -> 1 / 2 (\[CapitalDelta] + \[CapitalDelta][1] - \[CapitalDelta][2]),
	b -> 1 / 2 (\[CapitalDelta] - \[CapitalDelta][1] + \[CapitalDelta][2]),
	c -> \[CapitalDelta] - d/2 + 1
} // Collect[#, f_[\[Xi]], Factor] &


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 2}], d -> 2};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][2])^(-\[CapitalDelta][1]) (2 x[2][2])^(-\[CapitalDelta][2]);


expr = (1/x[2][2] (I d[1][1] x[1][0] x[1][2]+d[1][1] x[1][1] x[1][2]-I d[1][1] x[1][2] x[2][0]
-d[1][1] x[1][2] x[2][1]-I d[1][1] x[1][0] x[2][2]+d[1][1] x[1][1] x[2][2]-d[2][2] x[1][2] x[2][2]
+I d[1][1] x[2][0] x[2][2]-d[1][1] x[2][1] x[2][2]+d[2][2] x[2][2]^2
-d[1][2] (x[1][0]^2+x[1][1]^2-2 x[1][0] x[2][0]+x[2][0]^2-2 x[1][1] x[2][1]+x[2][1]^2-x[1][2] x[2][2]
+x[2][2]^2)+d[1][0] (-x[1][2] x[2][0]+I x[1][2] x[2][1]-I x[1][1] (x[1][2]-x[2][2])-x[2][0] x[2][2]
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


expr = (
	-((d[1][0] x[1][0] x[1][2])/(x[1][2]+x[2][2]))-(I d[1][1] x[1][0] x[1][2])/(x[1][2]+x[2][2])
	+(I d[1][0] x[1][1] x[1][2])/(x[1][2]+x[2][2])-(d[1][1] x[1][1] x[1][2])/(x[1][2]+x[2][2])-(d[1][2] x[1][2]^2)/(x[1][2]+x[2][2])
	+(d[1][0] x[1][2] x[2][0])/(x[1][2]+x[2][2])+(I d[1][1] x[1][2] x[2][0])/(x[1][2]+x[2][2])-(I d[1][0] x[1][2] x[2][1])/(x[1][2]+x[2][2])
	+(d[1][1] x[1][2] x[2][1])/(x[1][2]+x[2][2])+(d[1][2] x[1][2] x[2][2])/(x[1][2]+x[2][2])
	-(2 \[CapitalDelta]p x[1][2])/(x[1][2]+x[2][2]) pref f[inv]
	+ \[CapitalDelta]p pref f[inv]
) /. d[i_][\[Mu]_] :> D[pref f[inv], x[i][\[Mu]]];
expr = (expr /. {inv -> \[Xi]}) / pref /. \[CapitalDelta][_] -> \[CapitalDelta]p // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &


diffEqf = (
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
	(* -2 \[Xi] f'[\[Xi]]
	- \[CapitalDelta] f[\[Xi]] *)
) // Collect[#, G_[\[Xi]], Simplify] &
(z^(-d-1) diffEqf /. f -> ((-1/#)^d ft[-1/#] &) /. \[Xi] -> -1/z
)// Collect[#, f_[z], Collect[#, z, Simplify]&] &


sol = Solve[{
	-2 d+d^2-(-2+\[CapitalDelta]) \[CapitalDelta] == 0,
	1/2 (d-2 d^2) == - a b,
	-1+2 d == c,
	(-(1/2)-2 d) == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


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


Solve[a-2 d+d^2+\[CapitalDelta]-\[CapitalDelta]^2==0, d] /. a -> 3/4 // FullSimplify[#, \[CapitalDelta]


Solve[1-a+(-1+\[CapitalDelta]) \[CapitalDelta] == 0, \[CapitalDelta]]


Solve[1/2 (1-Sqrt[-3+4 a])==1/2 (1+Sqrt[-3+4 a]),a] // Expand


-1/2r^2 /. r -> r-2 // Expand
-1/2r^2 /. r -> r-1 // Expand
-1/2r^2 /. r -> r   // Expand
-1/2r^2 /. r -> r+1 // Expand
-1/2r^2 /. r -> r+2 // Expand


sol = Solve[{
	-d+d^2+\[CapitalDelta]-\[CapitalDelta]^2 == 0,
	1/2 (d-2 d^2) == - a b,
	2 d == c,
	(-(1/2)-2 d) == -(a + b + 1)
}, {a, b, c, d}];
\[Xi]^(-d) Hypergeometric2F1[a, b, c, -1/\[Xi]] /. sol // DeleteDuplicates


diffEqf /. f -> (#^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-1/2, 2\[CapitalDelta], -1/#] &) // FullSimplify






(* ::Subsection::Closed:: *)
(*4d boundary*)


inv = \[Xi]v /. {dot[a_, b_] :> Sum[a[\[Mu]] b[\[Mu]], {\[Mu], 0, 3}], d -> 3};
restoreInv = Solve[inv == \[Xi], x[1][0]] // First;
pref = (2 x[1][3])^(-\[CapitalDelta][1]) (2 x[2][3])^(-\[CapitalDelta][2]);


(* ::Subsubsection:: *)
(*Defect channel*)


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


(* ::Subsubsection:: *)
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
	+ 4 \[Xi]^2 (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]]
	+ 4 \[Xi] (-1+\[Xi]+2 \[CapitalDelta]p (1+\[Xi])) Derivative[1][f][\[Xi]]
	+ (4 \[CapitalDelta]-\[CapitalDelta]^2+4 \[CapitalDelta]p (-2+\[CapitalDelta]p+\[CapitalDelta]p \[Xi])) f[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] Derivative[1][f][\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]]


(* ::Subsection:: *)
(*Accross dimensions*)


(* ::Subsubsection:: *)
(*Defect channel*)


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


defectSusyBlock[\[CapitalDelta], d][\[Xi]] 


diff = (
	+ defectSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		defectBlock[\[CapitalDelta], d][\[Xi]]
		+ \[CapitalDelta]/(4\[CapitalDelta] - 2d + 6) defectBlock[\[CapitalDelta]+1, d][\[Xi]]
	)a[1]
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


(* ::Subsubsection:: *)
(*Bulk channel*)


bulkBlock[\[CapitalDelta]_, \[CapitalDelta]1_, \[CapitalDelta]2_, d_][\[Xi]_] :=(
	\[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[(\[CapitalDelta]+\[CapitalDelta]1-\[CapitalDelta]2)/2, (\[CapitalDelta]-\[CapitalDelta]1+\[CapitalDelta]2)/2, \[CapitalDelta]+1-d/2, -\[Xi]]
);
bulkSusyBlock[\[CapitalDelta]_, d_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2, \[CapitalDelta]/2, \[CapitalDelta]+2-d/2, -\[Xi]]
randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}


diffEqf = (
	+ f[\[Xi]] (-\[CapitalDelta]^2+\[CapitalDelta][1]^2+d (\[CapitalDelta]-\[CapitalDelta][1]-\[CapitalDelta][2])+2 \[CapitalDelta][1] \[CapitalDelta][2]+4 \[Xi] \[CapitalDelta][1] \[CapitalDelta][2]+\[CapitalDelta][2]^2)
	+(-2 d \[Xi]+4 \[Xi] (1+\[Xi]) (1+\[CapitalDelta][1]+\[CapitalDelta][2])) f'[\[Xi]]
	+4 \[Xi]^2 (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &
diffEqG = (
	\[Xi]^((\[CapitalDelta][1]+\[CapitalDelta][2])/2) diffEqf 
		/. f -> (#^(-(\[CapitalDelta][1]+\[CapitalDelta][2])/2) G[#] &) 
		// Collect[#, G_[\[Xi]], Simplify] &
);
diffEqG /. G -> bulkBlock[\[CapitalDelta], \[CapitalDelta][1], \[CapitalDelta][2], d] /. randRules[\[CapitalDelta][_], \[CapitalDelta], \[Xi], d]
(* DSolve[diffEqf == 0, f[\[Xi]], \[Xi]]
DSolve[diffEqG == 0, G[\[Xi]], \[Xi]] *)


diffEqf = (
	+ (-\[CapitalDelta]^2+d (\[CapitalDelta]-2 \[CapitalDelta]p)+4 \[CapitalDelta]p^2 (1+\[Xi])) f[\[Xi]]
	+ (-2 d \[Xi]+4 (1+2 \[CapitalDelta]p) \[Xi] (1+\[Xi])) f'[\[Xi]]
	+ 4 \[Xi]^2 (1+\[Xi]) f''[\[Xi]]
	+ 4 \[CapitalDelta]p f[\[Xi]]+4 \[Xi] f'[\[Xi]]
	- 2 \[CapitalDelta] f[\[Xi]]
) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG = \[Xi]^\[CapitalDelta]p diffEqf /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, G_[\[Xi]], Simplify] &;
diffEqG /. G -> bulkSusyBlock[\[CapitalDelta], d] /. randRules[\[CapitalDelta], \[Xi], d]
(* DSolve[diffEqG == 0, G[\[Xi]], \[Xi]] *)


 bulkSusyBlock[\[CapitalDelta], d][\[Xi]] 


diff = (
	+ bulkSusyBlock[\[CapitalDelta], d][\[Xi]] 
	- (
		+ bulkBlock[\[CapitalDelta], 0, 0, d][\[Xi]]
		+ \[CapitalDelta]^2/((2\[CapitalDelta] + 2 - d)(2\[CapitalDelta] + 4 - d)) bulkBlock[\[CapitalDelta]+2, 0, 0, d][\[Xi]]
	)
) /. randRules[\[CapitalDelta], d, \[Xi]]


(* ::Section:: *)
(*Philine's results*)


(* ::Subsection::Closed:: *)
(*(2,0) bulk channel*)


Clear[block]
diffEq = 4 \[Xi]^2 (\[Xi] + 1) G''[\[Xi]] + 2\[Xi](1 + 4\[Xi]) G'[\[Xi]] - \[CapitalDelta](\[CapitalDelta]-1) G[\[Xi]]
block[\[CapitalDelta]_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2, \[CapitalDelta]/2, \[CapitalDelta]-1/2, -\[Xi]];
solSum     = G -> (block[\[CapitalDelta]][#] - (\[CapitalDelta]-1)\[CapitalDelta]/((2\[CapitalDelta]-1)(2\[CapitalDelta]+1)) block[\[CapitalDelta]+2][#] &);
solCompact = G -> (#^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2+1, \[CapitalDelta]/2, \[CapitalDelta]+1/2, -#] &);
diffEq /. solCompact // FullSimplify


lhs = \[Xi]^-\[CapitalDelta]p diffEq /. G -> (#^\[CapitalDelta]p f[#] &) // Collect[#, f_[\[Xi]], Simplify] &
rhs = (
	+(3 \[CapitalDelta]-\[CapitalDelta]^2+2 \[CapitalDelta]p (-3+2 \[CapitalDelta]p (1+\[Xi]))) f[\[Xi]]
	+2 \[Xi] (-1+2 \[Xi]+4 \[CapitalDelta]p (1+\[Xi])) Derivative[1][f][\[Xi]]
	+4 \[Xi]^2 (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]]
);
lhs - rhs // Collect[#, f_[\[Xi]], Simplify] &


(3 \[CapitalDelta]-\[CapitalDelta]^2+2 \[CapitalDelta]p (-3+2 \[CapitalDelta]p (1+\[Xi]))) f[\[Xi]]+2 \[Xi] (-1+2 \[Xi]+4 \[CapitalDelta]p (1+\[Xi])) Derivative[1][f][\[Xi]]+4 \[Xi]^2 (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]] // Collect[#, f_[\[Xi]], Simplify] &


finDiffEq = (
	+ (\[CapitalDelta]-\[CapitalDelta]^2+2 \[CapitalDelta]p (-3+2 \[CapitalDelta]p (1+\[Xi]))) f[\[Xi]]
	+ 2 \[Xi] (-1+2 \[Xi]+4 \[CapitalDelta]p (1+\[Xi])) Derivative[1][f][\[Xi]]
	+ 4 \[Xi]^2 (1+\[Xi]) (f^\[Prime]\[Prime])[\[Xi]]
	+ 4 \[CapitalDelta]p (1+\[Xi]) f[\[Xi]]+4 \[Xi] (1+\[Xi]) Derivative[1][f][\[Xi]]
) /. {\[CapitalDelta][_] -> \[CapitalDelta]p, d -> 3} // Collect[#, f_[\[Xi]], Simplify] &


 \[Xi]^\[CapitalDelta]p finDiffEq /. f -> (#^(-\[CapitalDelta]p) G[#] &) // Collect[#, f_[\[Xi]], Simplify] &


% /. solCompact // FullSimplify


(* ::Text:: *)
(*Check the two solutions are the same:*)


Series[(f[\[Xi]] /. solSum) - (f[\[Xi]] /. solCompact), {\[Xi], 0, 10}]


diffEq = (-z)^d (z(1-z)f''[z] + (c-(a+b+1)z) f'[z] - a b f[z] 
	/. {f -> (#^(-d) g[#] &)}
	/. {g -> (g[-#] &)}
	/. z -> -z
) // Collect[#, g_[z], Factor] &


DSolve[diffEq == 0, g[z], z]


4z diffEq /. {
	d -> \[CapitalDelta]/2,
	a -> \[CapitalDelta]/2+1,
	b -> \[CapitalDelta]/2,
	c -> \[CapitalDelta]+1/2
} // Collect[#, g_[z], Simplify] &


(* ::Subsection::Closed:: *)
(*(1,1) boundary channel*)


(
	+ \[Xi] (1+\[Xi]) f''[\[Xi]]
	+ 3/2 (1+2 \[Xi]) f'[\[Xi]]
	- \[CapitalDelta] (\[CapitalDelta]-2) f[\[Xi]]
) - (
\[Xi](1+\[Xi]) f''[\[Xi]]+(3/2+2 \[Xi]) f'[\[Xi]] - \[CapitalDelta](\[CapitalDelta]-1) f[\[Xi]]
) // Expand


Clear[block]
diffEq = (- 4\[Xi] - 12) f'[\[Xi]] + (-8\[Xi] - 2\[Xi]^2) f''[\[Xi]] - 2\[CapitalDelta](1-\[CapitalDelta]) f[\[Xi]]
diffEq = \[Xi](1+\[Xi]) f''[\[Xi]]+(3/2+2 \[Xi]) f'[\[Xi]] - \[CapitalDelta](\[CapitalDelta]-1) f[\[Xi]]
block[\[CapitalDelta]_][\[Xi]_] := \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta], \[CapitalDelta]-1/2, 2\[CapitalDelta]-1, -1/\[Xi]];
diffEq /. f -> (block[\[CapitalDelta]][#] + 1/4 block[\[CapitalDelta]+1][#] &) // FullSimplify


lhs = block[\[CapitalDelta]][\[Xi]] + 1/4 block[\[CapitalDelta]+1][\[Xi]];
rhs = \[Xi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta]-1/2, \[CapitalDelta], 2\[CapitalDelta], -1/\[Xi]];
lhs / rhs // FullSimplify


-1/y((-a (b+d)-d (b+d-y+c y+d y)) g[y]+y (-1+a+b+2 d-2 y+c y+2 d y) Derivative[1][g][y]-y^2 (1+y) (g^\[Prime]\[Prime])[y]) /. {
	a -> \[CapitalDelta]-1/2,
	b -> \[CapitalDelta],
	c -> 2\[CapitalDelta],
	d -> -\[CapitalDelta]
} // Simplify


diffEq = z(1-z) f''[z] + (c - (a+b+1)z) f'[z] - a b f[z];
y^(d) diffEq /. f -> ((-1/#)^(-d) g[-1/#]&) /. z -> -1/y // Collect[#, g_[y], Simplify] &
% /. g -> (#^d Hypergeometric2F1[a, b, c, -1/#] &) // FullSimplify


DSolve[(a (-b+d)-d (-b+d+y-c y+d y)) g[y]-y (1-a-b+2 d+2 y-c y+2 d y) Derivative[1][g][y]-y^2 (1+y) (g^\[Prime]\[Prime])[y]==0,
g[y], y]


Series[-((3 4^(-1+\[CapitalDelta]) (-1+2 \[CapitalDelta]) (1+Sqrt[1+1/\[Xi]])^(-2 \[CapitalDelta]) \[Xi]^(-2-\[CapitalDelta]) (-1+2 \[CapitalDelta] (1+\[Xi]+Sqrt[1+1/\[Xi]] \[Xi])))/(1+1/\[Xi])^(3/2)),{\[Xi],0,2}]


(* ::Subsection::Closed:: *)
(*(1,1) bulk channel*)


Clear[block]
diffEq = (- 4\[Xi] - 2\[Xi]^2) f'[\[Xi]] + (-8\[Xi]^2 - 2\[Xi]^3) f''[\[Xi]] + 2\[CapitalDelta](1-\[CapitalDelta]) f[\[Xi]]
block[\[CapitalDelta]_][\[Xi]_] := \[Xi]^(\[CapitalDelta]/2) Hypergeometric2F1[\[CapitalDelta]/2, \[CapitalDelta]/2, \[CapitalDelta]-1/2, -\[Xi]];
diffEq /. f -> (block[\[CapitalDelta]][#] + \[CapitalDelta]^2/((2\[CapitalDelta]-1)(2\[CapitalDelta]+1)) block[\[CapitalDelta]+2][#] &) // FullSimplify






