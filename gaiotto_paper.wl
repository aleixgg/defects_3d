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


(* ::Subsection::Closed:: *)
(*Only fermions*)


Grading[a_Plus]:=Max@@(Grading/@(List@@a));
Grading[a_Times]:=Plus@@(Grading/@(List@@a));
Grading[a_CenterDot]:=Plus@@(Grading/@(List@@a));
Grading[Unevaluated[Derivative[__][f_][x__]]]:=Grading[f[x]];
Grading[Unevaluated[GD[a_,b_]]]:=Grading[a]+Grading[b];
Grading[_]:=0;
NumQ[_]:=False;
NumQ[a_?NumericQ]:=True;
Fermion[a__]:=(Grading[#]=1)&/@{a};
Boson[a__]:=(Grading[#]=2)&/@{a};
SetNumeric[a__]:=(NumQ[#]=True)&/@{a};

(* GD[a_,b_,c__]:=GD[GD[a,b],c];*)
GD[GD[a_,b_],b_]:=0/;OddQ[Grading[b]];
GD[GD[a_,b_],c_]/;Not@OrderedQ[{b,c}]:=(-1)^(Grading[b]Grading[c]) GD[GD[a,c],b];
(* GD[a_,b_,c_]:=If[OrderedQ[b,c],GD[GD[a,b],c],(-1)^Grading[b\[CenterDot]c] GD[GD[a,c],b]]; *)
(* GD[a_,a_]:=1; *)
(* GD[a_,b_]:=0/;FreeQ[a,b]; *)
GD[a_,b_]:=0/;NumQ[a];
GD[a_+b_,c_]:=GD[a,c]+GD[b,c];
GD[a_ b_,c_]:=GD[b,c]\[CenterDot]a+GD[a,c]\[CenterDot]b;
GD[a_\[CenterDot]b_,c_]:=GD[a,c]\[CenterDot]b+(-1)^(Grading[a]Grading[c]) a\[CenterDot]GD[b,c];
GD[a_\[CenterDot]b__,c_]:=GD[a,c]\[CenterDot]CenterDot[b]+(-1)^(Grading[a]Grading[c]) a\[CenterDot]GD[CenterDot[b],c];
GD[a_^b_,c_]/;EvenQ@Grading@a:=b a^(b-1) GD[a,c];
SetAttributes[GD,Listable];
(*Unprotect[D];
(*Need to make sure that the chain rule for ordinary derivatives is compatible with GD[a_,b_]:=0/;FreeQ[a,b]!*)
D[Unevaluated[c_. (d_: 1)\[CenterDot]GD[a_,g_]\[CenterDot](e_: 1)+f_.],b__]:=D[c,b] d\[CenterDot]GD[a,g]\[CenterDot]e+c D[d,b]\[CenterDot]GD[a,g]\[CenterDot]e+c d\[CenterDot]GD[D[a,b],g]\[CenterDot]e+c d\[CenterDot]GD[a,g]\[CenterDot]D[e,b]+D[f,b];
Protect[D];*)

SetAttributes[CenterDot,Listable];
CenterDot[a___,b_CenterDot,c___]:=CenterDot[a,Sequence@@b,c];

(*Modified by J.Michelson,Nov.2006. The modifications also introduce GetGradeds and and GetFermions which act as a "cache".This might,of course,also act as a memory leak.A smarter cache keep only the last n results.GetGradeds[a,b,...] returns a list of only those arguments that have a nonzero Grading.GetFermions[a,b,...] returns a list of those arguments that are Grassmann.*)
GetGradeds[a___]:=GetGradeds[a]=Select[{a},Grading[#]!=0&];
GetFermions[a___]:=GetFermions[a]=Select[{a},OddQ[Grading[#]]&];
(*First make sure purely commutative stuff,for which OrderedQ[{}]\[Equal]True,or products with only one noncommutative factor,come out right.As a byproduct,this will fix the CenterDot[] is not simplified bug.*)

CenterDot[a___]/;Length[GetGradeds[a]]<=1:=Times[a];
(*Next do the a\[CenterDot](b c) rule with minimal recursion.If we had used Times\[Rule]CenterDot,then when combined with the flatness property of CenterDot,this might work.However,it would then cause infinite recursion in a\[CenterDot](b c+d e)\[CenterDot]f,if we.If we check for Times at only at level 2 to match a\[CenterDot](b c)\[CenterDot]f but not the Times inside a sum,then we can automatically implement the Flatness of CenterDot but doing Times\[Rule]Sequence,and then we don't have to worry about Mathematica getting the rules right.Finally,we hav to be careful to only replace the Times that are at the right level,so that e.g.a\[CenterDot](b c)\[CenterDot](d e+f g)\[Rule]a\[CenterDot]b\[CenterDot]c\[CenterDot](d e+f g),not a\[CenterDot]b\[CenterDot]c\[CenterDot](d+e+f+g)! A final implementation note:Replace[{a},Rule,2] didn't work,so I had to use the ReplacePart.*)

CenterDot[a___]/;!FreeQ[{a},Times,2]:=CenterDot@@ReplacePart[{a},Sequence,Position[{a},Times,2]];
(*Now the general case.The second test in the condition is to ensure that e.g.3\[CenterDot]epsilon,which is Ordered,still gets simplified,without incurring infinite recursion.The first definition replaces the a_\[CenterDot]a_:=0 rule;it is tempting to make it a third test in the condition of the general case,but that creates an endless loop.*)
CenterDot[b___,a_,c___,a_,d___]/;OddQ[Grading[a]]:=0;
CenterDot[a___]/;(!OrderedQ[GetGradeds[a]]||Length[GetGradeds[a]]!=Length[{a}]):=Signature[GetFermions[a]]*(Times@@Select[{a},!MemberQ[GetGradeds[a],#]&])*CenterDot@@Sort[GetGradeds[a]];
(*The reason for the cache is now (almost) obvious.Module[{g=GetGradeds[a]},...] would still require an extra call to GetGradeds do to the "/;".However,if we were so inclined,we could do Module[{result},result= <above>;GetGradeds[a]=.;Return[result]] to avoid the memory leak.*)

GPower[x_,n_Integer?Positive]:=Nest[x\[CenterDot]#&,x,n-1];
GExpand[a_,patt___]:=Expand[a//.{x_CenterDot:>Distribute[x]},patt];
GCollect[a_,b_List]:=Inner[CenterDot,Outer[CenterDot,Sequence@@({1,-#}&/@b)]//Flatten,Transpose[Fold[{#1/.#2->0,-GD[#1,#2]}&,a,b],Reverse[Range[Length[b]]]]//Flatten];
(*Jeremy Michelson's documentation on (understanding of) Matt's GCollect:Suppose b has n elements:
*Fold[....] makes a 2-dimensional rank n tensor with Fold[....][[i1,...,in]]=(-1)^(# of i's that are 2)*GD[...[GD[a,b[[first i that is 2]]],...],b[[last i that is 2]]]/.{b[[first i that is 1]]\[Rule]0,...,b[[last i that is 1]]\[Rule]0}*Reverse the order of indices and then flatten the list,so we now have {expr/.{b[[1]]\[Rule]0,...,b[[n]]\[Rule]0},-GD[expr,b[[n]]]/.{b[[1]]\[Rule]0,...,b[[n-1]]\[Rule]0},-GD[expr,b[[n-1]]]/.{b[[1]]\[Rule]0,...,b[[n-2]]\[Rule]0,b[[n]]\[Rule]0},...,}*Multiply the ith of these 2^n expressions with the ith of the 2^n expressions from the Outer,namely,{1,-b[n],-b[n-1],b[n-1]\[CenterDot]b[n],...} and sum.Since b's are assumed to be Grassmann,this is equivalent to the original expression,but now the terms are grouped.The sign of each term is correct because GD was programmed correctly.The reason for including explicit signs here is...?*)

CollectCD[expr_,fun_:Identity]:=Collect[expr,HoldPattern[CenterDot[___]],fun]
ClearAll[GCoefficient];
GCoefficient[expr_,a__CenterDot]:=Fold[GD[#1,#2]&,expr,List@@a]
GCoefficient[expr_,b_ a__CenterDot]:=1/b GCoefficient[expr,a]
GCoefficient[expr_,1]:=expr

ErrorMsg::notConverged="The algorithm did not converge";
SetAttributes[expExpr,Listable];
expExpr[expr_]:=Module[{out,i},
	out[0]=1;
	For[i=1,out[i-1]=!=0&&i<10,i++,out[i]=CollectCD[#,Factor]&@GExpand[out[i-1]\[CenterDot]expr]/i];
	If[i==10,Message[ErrorMsg::notConverged]];
	Total[out/@Range[0,i-1]]
];

SetAttributes[powerExpr,Listable];
powerExpr[expr_,power_,patt_:(\[Theta]|\[Xi])]:=Module[{myexpr,coef,param,out,i},
	myexpr=GExpand@Together@expr;
	coef=If[Head[myexpr]===Plus,Factor[Plus@@Select[List@@myexpr,FreeQ[#,patt]&]],myexpr];
	If[coef===myexpr,coef^power,
		param=CollectCD[#,Factor]&@Together[myexpr/coef-1];
		out[0]=1;
		For[i=1,out[i-1]=!=0&&i<10,i++,out[i]=CollectCD[#,Factor]&@GExpand[out[i-1]\[CenterDot]param] (power-i+1)/i];
		If[i==10,Message[ErrorMsg::notConverged]];
		coef^power Total[out/@Range[0,i-1]]
	]
];

SetAttributes[expandDen,Listable];
expandDen[expr_]:=Module[{num,den,denInv,param,coef,one},
	num=GExpand@Numerator@Together[expr];
	den=GExpand@Denominator@Together[expr];
	CollectCD[#,Factor]&@GExpand[num\[CenterDot]powerExpr[den,-1]]
];


(* ::Subsubsection::Closed:: *)
(*Tests*)


runTests:=Module[{\[Theta],i,\[CapitalDelta],x,expr1,expr2,expr3,expr4,expr5,expr\[CapitalDelta],test1,test2},
	Fermion[\[Theta][_]];
	expr1=Sum[\[Theta][i]\[CenterDot]\[Theta][7-i],{i,3}];
	expr2=expr1\[CenterDot]expr1//GExpand;
	expr3=expr2\[CenterDot]expr1//GExpand;
	expr4=expr3\[CenterDot]expr1//GExpand;
	expr5=expr4\[CenterDot]expr1//GExpand;
	test1=expExpr[expr1]-(1+expr1+1/2!expr2+1/3!expr3+1/4!expr4+1/5!expr5)==0//GExpand;
	expr1=x+Sum[\[Theta][i]\[CenterDot]\[Theta][7-i],{i,3}];
	expr2=expr1\[CenterDot]expr1//GExpand;
	expr3=expr2\[CenterDot]expr1//GExpand;
	expr4=expr3\[CenterDot]expr1//GExpand;
	expr5=expr4\[CenterDot]expr1//GExpand;
	expr\[CapitalDelta]=powerExpr[expr1,\[CapitalDelta],\[Theta]];
	test2={
		(expr\[CapitalDelta]/.{\[CapitalDelta]->2})-expr2==0//GExpand,
		(expr\[CapitalDelta]/.{\[CapitalDelta]->3})-expr3==0//GExpand,
		(expr\[CapitalDelta]/.{\[CapitalDelta]->4})-expr4==0//GExpand,
		(expr\[CapitalDelta]/.{\[CapitalDelta]->-2})\[CenterDot]expr2-1==0//GExpand,
		(expr\[CapitalDelta]/.{\[CapitalDelta]->-3})\[CenterDot]expr3-1==0//GExpand,
		(expr\[CapitalDelta]/.{\[CapitalDelta]->-4})\[CenterDot]expr4-1==0//GExpand,
		expandDen[1/expr1]\[CenterDot]expr1-1==0//GExpand,
		expandDen[1/expr2]\[CenterDot]expr2-1==0//GExpand
	};
	{test1,test2}//GExpand//Flatten//DeleteDuplicates
]
runTests


(* ::Subsection::Closed:: *)
(*Blocks recursion*)


hInfR[\[CapitalDelta]12_, \[CapitalDelta]34_][r_, \[Eta]_, d_] := (
	1 / (
	(1 - r^2)^((d-2)/2)
	(1 + r^2 + 2 r \[Eta])^((1+\[CapitalDelta]12-\[CapitalDelta]34)/2) 
	(1 + r^2 - 2 r \[Eta])^((1-\[CapitalDelta]12+\[CapitalDelta]34)/2)
));
hInfEta[l_, \[CapitalDelta]12_, \[CapitalDelta]34_][\[Eta]_, d_] := (l! GegenbauerC[l, (d-2)/2, \[Eta]]) / Pochhammer[d-2, l];
hInfRSer[\[CapitalDelta]12_, \[CapitalDelta]34_][r_, \[Eta]_, d_, maxOrd_] := hInfRSer[\[CapitalDelta]12, \[CapitalDelta]34][r, \[Eta], d, maxOrd] =
	Series[hInfR[\[CapitalDelta]12, \[CapitalDelta]34][r, \[Eta], d], {r, 0, maxOrd}] // ExpandAll;
hInfSer[l_, \[CapitalDelta]12_, \[CapitalDelta]34_][r_, \[Eta]_, d_, maxOrd_] := ExpandAll[
	hInfEta[l, \[CapitalDelta]12, \[CapitalDelta]34][\[Eta], d]
	hInfRSer[\[CapitalDelta]12, \[CapitalDelta]34][r, \[Eta], d, maxOrd]
]


(* Evaluate a partial fraction at \[CapitalDelta]=a *)
evalPartialFraction[PartialFraction[pol_, rs_], \[CapitalDelta]_, a_] := (
	+ (pol /. \[CapitalDelta] -> a) 
	+ (1 / (a - (First/@rs))) . (Last /@ rs)
);


cbRecurse[LMax_, \[CapitalDelta]12_, \[CapitalDelta]34_, d_, order_] := Module[
	{h, \[Alpha], \[Beta], \[Gamma], maxPoleOrder, LMaxRecursion, dd, \[Nu] = (d-2)/2, blocks},

	LMaxRecursion = LMax + order;
	maxPoleOrder[L_] := Min[order, LMaxRecursion-L];
	h[\[CapitalDelta]0_, l_] := evalPartialFraction[blocks[[l+1]], \[CapitalDelta], \[CapitalDelta]0];

	\[Alpha][n_, L_] := -((4^n n)/(n!)^2) Pochhammer[1/2 (1-n+\[CapitalDelta]12),n] Pochhammer[1/2 (1-n+\[CapitalDelta]34),n] Pochhammer[2\[Nu]+L,n]/Pochhammer[\[Nu]+L,n];
	\[Beta][k_, L_] := -(4^(2 k) k (-1)^k Pochhammer[-k+\[Nu],2 k] Pochhammer[1/2 (1-k+L-\[CapitalDelta]12+\[Nu]),k] Pochhammer[1/2 (1-k+L+\[CapitalDelta]12+\[Nu]),k] Pochhammer[1/2 (1-k+L-\[CapitalDelta]34+\[Nu]),k] Pochhammer[1/2 (1-k+L+\[CapitalDelta]34+\[Nu]),k])/((k!)^2 Pochhammer[-k+L+\[Nu],2 k] Pochhammer[1-k+L+\[Nu],2 k]);
	\[Gamma][n_, L_] := -((4^n n)/(n!)^2) Pochhammer[1/2 (1-n+\[CapitalDelta]12),n] Pochhammer[1/2 (1-n+\[CapitalDelta]34),n] Pochhammer[1+L-n,n]/Pochhammer[1+\[Nu]+L-n,n];

	blocks = Table[
		PartialFraction[hInfSer[L, \[CapitalDelta]12, \[CapitalDelta]34][r, \[Eta], d, maxPoleOrder[L]], {}]
	, {L, 0, LMaxRecursion}];
	Do[
		WriteString["stdout", recursionSteps, ", "];
		blocks = Table[PartialFraction[
			blocks[[L+1,1]],
			Join[
				Table[{-(n+L-1), \[Alpha][n, L] r^n h[1-L, L+n]}, {n, maxPoleOrder[L]}],
				Table[{-(-\[Nu]+k-1), \[Beta][k, L] r^(2k) h[1+\[Nu]+k, L]}, {k, maxPoleOrder[L]/2}],
				Table[{-(-L-2\[Nu]+n-1), \[Gamma][n, L] r^n h[L+2\[Nu]+1, L-n]}, {n, Min[maxPoleOrder[L], L]}]
			] // ExpandAll
		], {L, 0, LMaxRecursion}]
	, {recursionSteps, order}];

	(4r)^\[CapitalDelta] Collect[Table[
		(Factor[Pochhammer[dd-2, L] / Pochhammer[dd/2-1, L]] /. dd -> d)
		Normal[evalPartialFraction[blocks[[L+1]], \[CapitalDelta], \[CapitalDelta]]]
		, {L, 0, LMax}], {r, \[Eta]}, Factor@*Together]
];


(* ::Section:: *)
(*Conventions*)


(* ::Text:: *)
(*Spacetime dimension*)


d = 3;
randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}


(* ::Subsection:: *)
(*Gamma matrices*)


Clear[\[Delta], \[Gamma]]

\[Delta] = KroneckerDelta;
\[Eta][0, 0] = -1; \[Eta][1, 1] = +1; \[Eta][2, 2] = +1;
\[Epsilon]up[1, 2] = +1; \[Epsilon]up[2, 1] = -1; \[Epsilon]up[1, 1] = \[Epsilon]up[2, 2] = 0;
\[Epsilon]dw[1, 2] = -1; \[Epsilon]dw[2, 1] = +1; \[Epsilon]dw[1, 1] = \[Epsilon]dw[2, 2] = 0;

\[Gamma][0][\[Alpha]_, \[Beta]_] := - IdentityMatrix[2][[\[Alpha], \[Beta]]];
\[Gamma][1][\[Alpha]_, \[Beta]_] := PauliMatrix[1][[\[Alpha], \[Beta]]];
\[Gamma][2][\[Alpha]_, \[Beta]_] := PauliMatrix[3][[\[Alpha], \[Beta]]];


(* ::Subsection:: *)
(*Collect differential operators 3d*)


SetNumeric[\[CapitalDelta][_]];
SetNumeric[r[_]];
(* Thetas always have the \[Alpha] index up *)
Fermion[\[Theta][_][_], \[Theta]b[_][_]];
GD[x[i_][\[Mu]_],   x[j_][\[Nu]_]]  := \[Delta][i, j] \[Delta][\[Mu], \[Nu]];
GD[x[_][_],     \[Theta][_][_]]    := 0;
GD[x[_][_],     \[Theta]b[_][_]]   := 0;
GD[\[Theta][i_][\[Alpha]_],   \[Theta][j_][\[Beta]_]]  := \[Delta][i, j] \[Delta][\[Alpha], \[Beta]];
GD[\[Theta][_][_],     x[_][_]]    := 0;
GD[\[Theta][_][_],     \[Theta]b[_][_]]   := 0;
GD[\[Theta]b[i_][\[Alpha]_],  \[Theta]b[j_][\[Beta]_]] := \[Delta][i, j] \[Delta][\[Alpha], \[Beta]];
GD[\[Theta]b[_][_],    x[_][_]]    := 0;
GD[\[Theta]b[_][_],    \[Theta][_][_]]    := 0;


cov\[ScriptCapitalD][\[Alpha]_][i_][expr_] := (
	+ GD[expr, \[Theta][i][\[Alpha]]]
	+ I Sum[\[Gamma][\[Mu]][\[Alpha], \[Beta]] \[Theta]b[i][\[Beta]] \[CenterDot] GD[expr, x[i][\[Mu]]], {\[Mu], 0, 2}, {\[Beta], 2}]
);
cov\[ScriptCapitalD]b[\[Alpha]_][i_][expr_] := (
	- GD[expr, \[Theta]b[i][\[Alpha]]]
	- I Sum[\[Gamma][\[Mu]][\[Alpha], \[Beta]] \[Theta][i][\[Beta]] \[CenterDot] GD[expr, x[i][\[Mu]]], {\[Mu], 0, 2}, {\[Beta], 2}]
);


(* ::Subsection:: *)
(*Chiral operator*)


SetNumeric[k1];
yV[i_][\[Mu]_] := x[i][\[Mu]] + I Sum[\[Gamma][\[Mu]][\[Alpha], \[Beta]] \[Theta][i][\[Alpha]] \[CenterDot] \[Theta]b[i][\[Beta]], {\[Alpha], 2}, {\[Beta], 2}];
GD[y[i_][\[Mu]_], a_] := GD[yV[i][\[Mu]], a];
Table[cov\[ScriptCapitalD]b[\[Alpha]][1][y[1][\[Mu]]], {\[Alpha], 2}, {\[Mu], 0, 2}]
