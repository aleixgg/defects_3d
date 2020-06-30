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


(* ::Subsection::Closed:: *)
(*Gamma matrices*)


Clear[\[Delta], \[CapitalSigma], \[CapitalSigma]b, m, mb]
\[Delta] = KroneckerDelta;
\[Epsilon]up[1, 2] = +1; \[Epsilon]up[2, 1] = -1; \[Epsilon]up[1, 1] = \[Epsilon]up[2, 2] = 0;
\[Epsilon]dw[1, 2] = -1; \[Epsilon]dw[2, 1] = +1; \[Epsilon]dw[1, 1] = \[Epsilon]dw[2, 2] = 0;
\[CapitalSigma][1][\[Alpha]_, \[Alpha]d_] := PauliMatrix[1][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][2][\[Alpha]_, \[Alpha]d_] := PauliMatrix[2][[\[Alpha], \[Alpha]d]];
(* \[CapitalSigma][2][\[Alpha]_, \[Alpha]d_] := - PauliMatrix[0][[\[Alpha], \[Alpha]d]]; *)
\[CapitalSigma][3][\[Alpha]_, \[Alpha]d_] := PauliMatrix[3][[\[Alpha], \[Alpha]d]];
\[CapitalSigma][4][\[Alpha]_, \[Alpha]d_] := I PauliMatrix[0][[\[Alpha], \[Alpha]d]]; 
\[CapitalSigma]b[\[Mu]_][\[Alpha]d_, \[Alpha]_] := Conjugate[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d]];
m[\[Mu]_, \[Nu]_][\[Alpha]_, \[Beta]_] := m[\[Mu], \[Nu]][\[Alpha], \[Beta]] = 1/4 Sum[
	\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]] -
	\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]]
, {\[Alpha]d, 2}];
mb[\[Mu]_, \[Nu]_][\[Alpha]d_, \[Beta]d_] := mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] = 1/4 Sum[
	\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d] -
	\[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Mu]][\[Alpha], \[Beta]d]
, {\[Alpha], 2}];


(* ::Subsection::Closed:: *)
(*Checks *)


(* ::Text:: *)
(*Eq. (9)*)


Table[
	Sum[\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]], {\[Alpha]d, 2}] == 
	\[Delta][\[Alpha], \[Beta]] \[Delta][\[Mu], \[Nu]] + 2 m[\[Mu], \[Nu]][\[Alpha], \[Beta]]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates
Table[
	Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d], {\[Alpha], 2}] == 
	\[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Mu], \[Nu]] + 2 mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}, {\[Beta]d, 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (10)*)


Table[{
	Sum[
		\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Beta]] + 
		\[CapitalSigma][\[Nu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]]
	, {\[Alpha]d, 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha], \[Beta]]
}, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}, {\[Beta], 2}] // Flatten // DeleteDuplicates
Table[{
	Sum[
		\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Nu]][\[Alpha], \[Beta]d] + 
		\[CapitalSigma]b[\[Nu]][\[Alpha]d, \[Alpha]] \[CapitalSigma][\[Mu]][\[Alpha], \[Beta]d]
	, {\[Alpha], 2}] == 2 \[Delta][\[Mu], \[Nu]] \[Delta][\[Alpha]d, \[Beta]d]
}, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}, {\[Beta]d, 2}] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Eq. (14)*)


Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Mu], d}] == 2 d


(* d=2;
Table[
	Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] mb[\[Mu], \[Nu]][\[Delta]d, \[Gamma]d], {\[Mu], d}, {\[Nu], d}] 
	- 1/2 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Delta]d, \[Gamma]d]
	+ b \[Delta][\[Alpha]d, \[Gamma]d] \[Delta][\[Delta]d, \[Beta]d]
, {\[Alpha]d, 2}, {\[Beta]d, 2}, {\[Gamma]d, 2}, {\[Delta]d, 2}]
d=3;
Table[
	Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] mb[\[Mu], \[Nu]][\[Delta]d, \[Gamma]d], {\[Mu], d}, {\[Nu], d}] 
	- 1/2 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Delta]d, \[Gamma]d]
	+ \[Delta][\[Alpha]d, \[Gamma]d] \[Delta][\[Delta]d, \[Beta]d]
, {\[Alpha]d, 2}, {\[Beta]d, 2}, {\[Gamma]d, 2}, {\[Delta]d, 2}]
d=4;
Table[
	Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] mb[\[Mu], \[Nu]][\[Delta]d, \[Gamma]d], {\[Mu], d}, {\[Nu], d}] 
	- 2/2 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Delta]d, \[Gamma]d]
	+ 2 \[Delta][\[Alpha]d, \[Gamma]d] \[Delta][\[Delta]d, \[Beta]d]
, {\[Alpha]d, 2}, {\[Beta]d, 2}, {\[Gamma]d, 2}, {\[Delta]d, 2}] *)


(* ::Section:: *)
(*Bulk Algebra*)


(* ::Subsection::Closed:: *)
(*Commutation relations*)


Boson[\[ScriptCapitalD], \[ScriptCapitalP][_], \[ScriptCapitalK][_], \[ScriptCapitalM][_, _], \[ScriptCapitalR]];
Fermion[\[ScriptCapitalQ]p[_], \[ScriptCapitalQ]m[_], \[ScriptCapitalS]p[_], \[ScriptCapitalS]m[_]];

\[ScriptCapitalM][\[Mu]_, \[Nu]_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM][\[Nu], \[Mu]];
\[ScriptCapitalM][\[Mu]_, \[Mu]_] := 0;

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]],  \[ScriptCapitalP][\[Mu]]], {\[Mu], d}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]], -\[ScriptCapitalK][\[Mu]]], {\[Mu], d}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Nu]], 2(\[Delta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]])], {\[Mu], d}, {\[Nu], d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalM][\[Rho], \[Sigma]], -(
	+ \[Delta][\[Mu], \[Rho]] \[ScriptCapitalM][\[Nu], \[Sigma]]
	- \[Delta][\[Nu], \[Rho]] \[ScriptCapitalM][\[Mu], \[Sigma]]
	- \[Delta][\[Mu], \[Sigma]] \[ScriptCapitalM][\[Nu], \[Rho]]
	+ \[Delta][\[Nu], \[Sigma]] \[ScriptCapitalM][\[Mu], \[Rho]]
)], {\[Mu], d}, {\[Nu], d}, {\[Rho], d}, {\[Sigma], d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]], - (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])]
, {\[Mu], d}, {\[Nu], d}, {\[Rho], d}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]], - (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])]
, {\[Mu], d}, {\[Nu], d}, {\[Rho], d}];

Table[SetAntiCommutator[\[ScriptCapitalQ]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[\[CapitalSigma][\[Mu]][\[Alpha],\[Alpha]d] \[ScriptCapitalP][\[Mu]], {\[Mu], d}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalS]m[\[Alpha]], Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalK][\[Mu]], {\[Mu], d}]], {\[Alpha], 2}, {\[Alpha]d, 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 
	+ \[Delta][\[Alpha], \[Beta]] (\[ScriptCapitalD] - (d-1)/2 \[ScriptCapitalR]) 
	- Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}]]
, {\[Alpha], 2}, {\[Beta], 2}];
Table[SetAntiCommutator[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalQ]m[\[Beta]d], 
	+ \[Delta][\[Alpha]d, \[Beta]d] (\[ScriptCapitalD] + (d-1)/2 \[ScriptCapitalR]) 
	- Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}]]
, {\[Alpha]d, 2}, {\[Beta]d, 2}];

Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]p[\[Alpha]],  + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], d}, {\[Alpha],  2}];
Table[SetCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]m[\[Alpha]d], + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]m[\[Alpha]] , {\[Alpha],  2}]], {\[Mu], d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]p[\[Alpha]d], - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]p[\[Alpha]],  {\[Alpha],  2}]], {\[Mu], d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]m[\[Alpha]],  - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]m[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], d}, {\[Alpha] , 2}];

Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]p[\[Alpha]], Sum[m[\[Mu], \[Nu]][\[Alpha], \[Beta]] \[ScriptCapitalQ]p[\[Beta]], {\[Beta], 2}]]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d] \[ScriptCapitalQ]m[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]p[\[Alpha]d], -Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalS]p[\[Beta]d], {\[Beta]d, 2}]]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]m[\[Alpha]], -Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalS]m[\[Beta]], {\[Beta], 2}]]
, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}];

Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalQ]p[\[Alpha]],  +1/2 \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalQ]m[\[Alpha]d], +1/2 \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalS]p[\[Alpha]d], -1/2 \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalD], \[ScriptCapitalS]m[\[Alpha]],  -1/2 \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}];

Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalQ]p[\[Alpha]],  + \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalQ]m[\[Alpha]d], - \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalS]p[\[Alpha]d], + \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}];
Table[SetCommutator[\[ScriptCapitalR], \[ScriptCapitalS]m[\[Alpha]],  - \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}];


(* ::Subsection::Closed:: *)
(*Check Jacobi identities*)


allOperators = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalR]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], d}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}],
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
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[\[ScriptCapitalP][\[Mu]]\[CenterDot]\[ScriptCapitalK][\[Mu]] + \[ScriptCapitalK][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]], {\[Mu], d}]
	- 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}]
	- (d-1)/4 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 Sum[\[ScriptCapitalS]p[\[Alpha]d]\[CenterDot]\[ScriptCapitalQ]m[\[Alpha]d] - \[ScriptCapitalQ]m[\[Alpha]d]\[CenterDot]\[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]
	+ 1/2 Sum[\[ScriptCapitalS]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]] - \[ScriptCapitalQ]p[\[Alpha]]\[CenterDot]\[ScriptCapitalS]m[\[Alpha]], {\[Alpha], 2}]
);
Table[Commutator[\[ScriptCapitalC]2, op], {op, allOperators}] // Expand // Flatten // DeleteDuplicates


(* ::Section:: *)
(*Defect Algebras*)


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN] = (2,0) subalgebra (boundary d=3)*)


(* ::Text:: *)
(*Check that the subalgebra closes and satisfies Jacobi:*)


allDefOps = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalR]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 2}],
	{\[ScriptCapitalM][1, 2]},
	{\[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1], \[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]}
];
defOpsToZero = # -> 0 & /@ allDefOps;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-\[ScriptCapitalD] - I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][1] - I \[ScriptCapitalP][2]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][1] + I \[ScriptCapitalK][2]);
\[ScriptCapitalL]b[0]  = 1/2 (-\[ScriptCapitalD] + I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][1] + I \[ScriptCapitalP][2]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][1] - I \[ScriptCapitalK][2]);
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
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	- 1/2 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 Commutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates


(* ::Text:: *)
(*Casimir eigenvalue*)


Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	- 1/2 \[ScriptCapitalR]\[CenterDot]\[ScriptCapitalR]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1, 2] -> I l,
	\[ScriptCapitalR] -> r
} // Simplify


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN] = (1,1) subalgebra (boundary d=3)*)


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-\[ScriptCapitalD] - I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][1] - I \[ScriptCapitalP][2]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][1] + I \[ScriptCapitalK][2]);
\[ScriptCapitalG][+1/2] = +1 / Sqrt[2] (\[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1]);
\[ScriptCapitalG][-1/2] = -1 / Sqrt[2] (\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2]);
\[ScriptCapitalL]b[0]  = 1/2 (-\[ScriptCapitalD] + I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][1] + I \[ScriptCapitalP][2]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][1] - I \[ScriptCapitalK][2]);
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
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalK][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
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


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN] = 2 subalgebra (line d=3)*)


(* ::Text:: *)
(*Check that the subalgebra closes*)


allDefOps = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalK][3], \[ScriptCapitalP][3]},
	{\[ScriptCapitalR] - I \[ScriptCapitalM][1, 2]},
	{\[ScriptCapitalS]p[1], \[ScriptCapitalQ]p[1], \[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[1]}
];
defOpsToZero = Solve[allDefOps == 0, {\[ScriptCapitalD], \[ScriptCapitalK][3], \[ScriptCapitalP][3], \[ScriptCapitalR], \[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1], \[ScriptCapitalS]p[1], \[ScriptCapitalS]m[1]}] // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


(* ::Text:: *)
(*It can be mapped explicitly to \[ScriptCapitalN]=2 in one dimension*)


Clear[\[ScriptCapitalL], \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = -\[ScriptCapitalD];
\[ScriptCapitalL][+1] = \[ScriptCapitalP][3];
\[ScriptCapitalL][-1] = \[ScriptCapitalK][3];
\[ScriptCapitalJ][0] = 2 (\[ScriptCapitalR] - I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalG][+1/2]  = - \[ScriptCapitalQ]p[1];
\[ScriptCapitalG][-1/2]  = + \[ScriptCapitalS]p[1];
\[ScriptCapitalG]b[+1/2] = - \[ScriptCapitalQ]m[1];
\[ScriptCapitalG]b[-1/2] = + \[ScriptCapitalS]m[1];
eqs = Join[{
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n]]  - (m-n) \[ScriptCapitalL][m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalG][r]]  - (m/2 - r) \[ScriptCapitalG][m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalG]b[r]] - (m/2 - r) \[ScriptCapitalG]b[m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[AntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG]b[s]] - (\[ScriptCapitalL][r+s] + 1/2(r-s) \[ScriptCapitalJ][r+s]) , {r, -1/2, 1/2}, {s, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG][r]]  - \[ScriptCapitalG][m+r],  {m, 0, 0}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG]b[r]] + \[ScriptCapitalG]b[m+r], {m, 0, 0}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalJ][n]] - n \[ScriptCapitalJ][m+n], {m, -1, 1}, {n, 0, 0}]
}] // Expand // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2def = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 AntiCommutator[\[ScriptCapitalK][3], \[ScriptCapitalP][3]]
	+ (\[ScriptCapitalM][1, 2] + I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][1, 2] + I \[ScriptCapitalR])
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates // CollectCD


(* ::Text:: *)
(*Casimir eigenvalue*)


Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Commutator[\[ScriptCapitalK][3], \[ScriptCapitalP][3]]
	+ (\[ScriptCapitalM][1, 2] + I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][1, 2] + I \[ScriptCapitalR])
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1, 2] -> I(s-\[ScriptCapitalR])
} // Expand


(* ::Text:: *)
(*Contribution in the defect channel*)


(
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
) - (
	-I (\[ScriptCapitalM][1, 2] + I \[ScriptCapitalR])
	- \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]p[1]
	+ \[ScriptCapitalS]m[1]\[CenterDot]\[ScriptCapitalQ]p[1]
) // Expand


(* ::Subsection::Closed:: *)
(*OSP(1|4) subalgebra (boundary d=4)*)


(* ::Text:: *)
(*Check that the subalgebra closes:*)


Qs = {\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]};
Ss = {\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2]};
Conf = Flatten @ Join[
	{\[ScriptCapitalD]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 3}],
	Table[\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 1, 2}, {\[Nu], \[Mu]+1, 3}]
];
allDefOps = Join[Conf, Qs, Ss];
defOpsToZero = Solve[allDefOps == 0, Join[Conf, {\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]p[2], \[ScriptCapitalS]p[1], \[ScriptCapitalS]p[2]}]] // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2def = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 3}]
	- 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 3}, {\[Nu], 3}]
	+ 1/4 Commutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2]]
	- 1/4 Commutator[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates


(* ::Text:: *)
(*Casimir eigenvalue*)


(Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 3}]
	- 1/2 Sum[\[ScriptCapitalM][\[Mu], \[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], 3}, {\[Nu], 3}]
	+ 1/4 AntiCommutator[\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2]]
	- 1/4 AntiCommutator[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1,2]\[CenterDot]\[ScriptCapitalM][1,2] -> -l(l+1) - \[ScriptCapitalM][1,3]\[CenterDot]\[ScriptCapitalM][1,3] - \[ScriptCapitalM][2,3]\[CenterDot]\[ScriptCapitalM][2,3],
	\[ScriptCapitalR] -> r
}) - (
	+ \[CapitalDelta](\[CapitalDelta]-2)
	+ l(l+1)
) // Expand


(* ::Subsubsection:: *)
(**)


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN]=(2,0) subalgebra (surface d=4)*)


(* ::Text:: *)
(*Check that the subalgebra closes:*)


Qs = {\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]};
Ss = {\[ScriptCapitalS]m[1], \[ScriptCapitalS]p[1]};
Conf = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalM][1, 2] + 3/2 I a \[ScriptCapitalR], \[ScriptCapitalM][3, 4]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 3, d}]
];
allDefOps = Join[Conf, Qs, Ss];
defOpsToZero = Solve[allDefOps == 0, (allDefOps/.a->0)] /. a->1 // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Map to commutation relations*)


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2(- \[ScriptCapitalD] - I \[ScriptCapitalM][3, 4]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][3] - I \[ScriptCapitalP][4]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][3] + I \[ScriptCapitalK][4]);
\[ScriptCapitalL]b[0]  = 1/2 (- \[ScriptCapitalD] + I \[ScriptCapitalM][3, 4]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][3] + I \[ScriptCapitalP][4]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][3] - I \[ScriptCapitalK][4]);
\[ScriptCapitalJ][0] = I (\[ScriptCapitalM][1, 2] + 3/2 I \[ScriptCapitalR]);
\[ScriptCapitalG][+1/2]  = - \[ScriptCapitalQ]m[1] / Sqrt[2];
\[ScriptCapitalG][-1/2]  = + \[ScriptCapitalS]m[1] / Sqrt[2];
\[ScriptCapitalG]b[+1/2] = - \[ScriptCapitalQ]p[1] / Sqrt[2];
\[ScriptCapitalG]b[-1/2] = + \[ScriptCapitalS]p[1] / Sqrt[2];
eqs = Join[{
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL][n]]  - (m-n) \[ScriptCapitalL][m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalL]b[n]] - (m-n) \[ScriptCapitalL]b[m+n], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL][m], \[ScriptCapitalL]b[n]], {m, -1, 1}, {n, -1, 1}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalG][r]]  - (m/2 - r) \[ScriptCapitalG][m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalL]b[m], \[ScriptCapitalG]b[r]] - (m/2 - r) \[ScriptCapitalG]b[m+r],  {m, -1, 1}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG][r]]  - \[ScriptCapitalG][m+r],  {m, 0, 0}, {r, -1/2, 1/2}],
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG]b[r]] + \[ScriptCapitalG]b[m+r], {m, 0, 0}, {r, -1/2, 1/2}],
	Table[AntiCommutator[\[ScriptCapitalG][r], \[ScriptCapitalG]b[s]] - (\[ScriptCapitalL]b[r+s] + 1/2(r-s) \[ScriptCapitalJ][r+s]) , {r, -1/2, 1/2}, {s, -1/2, 1/2}]
}] // Expand // Flatten // DeleteDuplicates // Collect[#, \[ScriptCapitalD]|(\[ScriptCapitalP]|\[ScriptCapitalK]|\[ScriptCapitalM]|\[ScriptCapitalS]p|\[ScriptCapitalS]m|\[ScriptCapitalQ]p|\[ScriptCapitalQ]m)[__], Factor] &


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2defPar = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 3, d}]
	- \[ScriptCapitalM][3, 4]\[CenterDot]\[ScriptCapitalM][3, 4]
	+ 1/2(\[ScriptCapitalM][1, 2] + 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][1, 2] + 3/2 I \[ScriptCapitalR])
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2defPar, op], {op, (allDefOps /. a -> 1)}] // Expand // DeleteDuplicates // CollectCD


(* ::Text:: *)
(*Casimir eigenvalue*)


(Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 3, d}]
	- \[ScriptCapitalM][3, 4]\[CenterDot]\[ScriptCapitalM][3, 4]
	+ 1/2(\[ScriptCapitalM][1, 2] + 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][1, 2] + 3/2 I \[ScriptCapitalR])
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][3, 4] -> I l,
	\[ScriptCapitalM][1, 2] -> I (s - 3/2 \[ScriptCapitalR])
}) - (
	+ \[CapitalDelta](\[CapitalDelta]-1)
	+ l(l+1)
	- 1/2 s^2
) // Expand


(* ::Text:: *)
(*Contribution defect channel*)


(
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
) - (
	- \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]p[1]
	+ \[ScriptCapitalS]m[1]\[CenterDot]\[ScriptCapitalQ]p[1]
) // Expand


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN]=(1,1) subalgebra (surface d=4) (can it be done?!?)*)


{Q1, Q2} = {
	  \[ScriptCapitalQ]p[1]+ 0 \[ScriptCapitalQ]p[2] + 0 \[ScriptCapitalQ]m[1] + 0 \[ScriptCapitalQ]m[2], 
	0 \[ScriptCapitalQ]p[1]+ 1 \[ScriptCapitalQ]p[2] + 0 \[ScriptCapitalQ]m[1] + 0 \[ScriptCapitalQ]m[2]
} //. {
	c -> a b,
	a -> 0
};
AntiCommutator[Q1, Q1] // Collect[#, \[ScriptCapitalP][_], Factor] &
AntiCommutator[Q1, Q2] // Collect[#, \[ScriptCapitalP][_], Factor] &
AntiCommutator[Q2, Q2] // Collect[#, \[ScriptCapitalP][_], Factor] &


(* ::Text:: *)
(*Check that the subalgebra closes:*)


Qs = {\[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1], \[ScriptCapitalQ]p[2] + \[ScriptCapitalQ]m[1]};
Ss = {\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2], \[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2]};
Conf = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalM][1, 2]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 2}]
];
allDefOps = Join[Conf, Qs, Ss(*, {\[ScriptCapitalM][3, 4] - 3/2 I a \[ScriptCapitalR]}*)];
defOpsToZero = Solve[allDefOps == 0, Join[Conf, {\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]p[2], \[ScriptCapitalS]p[1], \[ScriptCapitalS]p[2], \[ScriptCapitalR]}]] // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Map to commutation relations*)


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-\[ScriptCapitalD] - I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][1] - I \[ScriptCapitalP][2]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][1] + I \[ScriptCapitalK][2]);
\[ScriptCapitalG][+1/2] = +1 / Sqrt[2] (\[ScriptCapitalQ]m[2] + \[ScriptCapitalQ]p[1]);
\[ScriptCapitalG][-1/2] = -1 / Sqrt[2] (\[ScriptCapitalS]m[1] + \[ScriptCapitalS]p[2]);
\[ScriptCapitalL]b[0]  = 1/2 (-\[ScriptCapitalD] + I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][1] + I \[ScriptCapitalP][2]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][1] - I \[ScriptCapitalK][2]);
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


\[ScriptCapitalC]2defPar = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	+ 1/2(\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])
	+ 1/2 Commutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2defPar, op], {op, (allDefOps /. a -> 1)}] // Expand // DeleteDuplicates // CollectCD


(* ::Text:: *)
(*Casimir eigenvalue*)


(Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	+ 1/2(\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1, 2] -> I l,
	\[ScriptCapitalM][3, 4] -> I (s + 3/2 \[ScriptCapitalR])
}) - (
	+ \[CapitalDelta](\[CapitalDelta]-1)
	+ l(l-1)
	- 1/2 s^2
) // Expand


(* ::Subsection::Closed:: *)
(*\[ScriptCapitalN]=2 subalgebra (line d=4)  (can it be done?!?)*)


{Q1, Q2} = {
	a1 \[ScriptCapitalQ]p[1] + a2 \[ScriptCapitalQ]p[2] + a3 \[ScriptCapitalQ]m[1] + a4 \[ScriptCapitalQ]m[2],
	b1 \[ScriptCapitalQ]p[1] + b2 \[ScriptCapitalQ]p[2] + b3 \[ScriptCapitalQ]m[1] + b4 \[ScriptCapitalQ]m[2]
};
sol = {
	a1 -> 1,
	a4 -> -a2 a3,
	a3 -> 0,
	b4 -> - a2 b3,
	b2 -> b1 a2
};
AntiCommutator[Q1, Q1] //. sol // Collect[#, \[ScriptCapitalP][_], Factor] &
AntiCommutator[Q1, Q2] //. sol // Collect[#, \[ScriptCapitalP][_], Factor] &
AntiCommutator[Q2, Q2] //. sol // Collect[#, \[ScriptCapitalP][_], Factor] &


(* ::Text:: *)
(*Check that the subalgebra closes:*)


AntiCommutator[\[ScriptCapitalQ]p


Qs = {\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]};
Ss = {\[ScriptCapitalS]m[1], \[ScriptCapitalS]p[2]};
Conf = Flatten @ Join[
	{\[ScriptCapitalD], \[ScriptCapitalM][1, 2], \[ScriptCapitalM][3, 4] - 3/2 I a \[ScriptCapitalR]}, 
	Table[{\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]}, {\[Mu], 2}]
];
allDefOps = Join[Conf, Qs, Ss];
defOpsToZero = Solve[allDefOps == 0, (allDefOps/.a->0)] /. a -> 1 // First;
allCombinations = Flatten[Outer[List, allDefOps, allDefOps], 1];
allCombinations = DeleteDuplicates[Sort /@ allCombinations];
(GradedCommutator @@@ allCombinations) /. defOpsToZero // Flatten // DeleteDuplicates




























(* ::Text:: *)
(*Map to commutation relations*)


Clear[\[ScriptCapitalL], \[ScriptCapitalL]b, \[ScriptCapitalJ], \[ScriptCapitalG], \[ScriptCapitalG]b];
\[ScriptCapitalL][0] = 1/2 (-\[ScriptCapitalD] - I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL][+1] = 1/2 (\[ScriptCapitalP][1] - I \[ScriptCapitalP][2]);
\[ScriptCapitalL][-1] = 1/2 (\[ScriptCapitalK][1] + I \[ScriptCapitalK][2]);
\[ScriptCapitalL]b[0]  = 1/2 (-\[ScriptCapitalD] + I \[ScriptCapitalM][1, 2]);
\[ScriptCapitalL]b[+1] = 1/2 (\[ScriptCapitalP][1] + I \[ScriptCapitalP][2]);
\[ScriptCapitalL]b[-1] = 1/2 (\[ScriptCapitalK][1] - I \[ScriptCapitalK][2]);
\[ScriptCapitalJ][0] = I (\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR]);
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


\[ScriptCapitalC]2defPar = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[AntiCommutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	+ 1/2(\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])
	+ 1/2 Commutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2defPar, op], {op, (allDefOps /. a -> 1)}] // Expand // DeleteDuplicates // CollectCD


(* ::Text:: *)
(*Casimir eigenvalue*)


(Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Sum[Commutator[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], 2}]
	- \[ScriptCapitalM][1, 2]\[CenterDot]\[ScriptCapitalM][1, 2]
	+ 1/2(\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])\[CenterDot](\[ScriptCapitalM][3, 4] - 3/2 I \[ScriptCapitalR])
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1, 2] -> I l,
	\[ScriptCapitalM][3, 4] -> I (s + 3/2 \[ScriptCapitalR])
}) - (
	+ \[CapitalDelta](\[CapitalDelta]-1)
	+ l(l-1)
	- 1/2 s^2
) // Expand


(* ::Section:: *)
(*Calculate blocks*)


(* ::Subsection::Closed:: *)
(*Action of generators*)


(* ::Text:: *)
(*Action using differential operators*)


xP = Sum[x[\[Mu]] \[ScriptCapitalP][\[Mu]], {\[Mu], d}];
expSer = 1 + xP + xP\[CenterDot]xP/2 + xP\[CenterDot]xP\[CenterDot]xP/6 // Expand;
truncate = HoldPattern@CenterDot[_, _, _, _] :> 0;
Table[
	lhs = \[ScriptCapitalP][\[Mu]]\[CenterDot]expSer; 
	rhs = D[expSer, x[\[Mu]]];
	lhs - rhs
, {\[Mu], d}] /. truncate //Expand // Flatten // DeleteDuplicates
Table[
	lhs = Commutator[\[ScriptCapitalM][\[Mu], \[Nu]], expSer];
	rhs = -(x[\[Mu]] D[expSer, x[\[Nu]]] - x[\[Nu]] D[expSer, x[\[Mu]]]);
	lhs - rhs
, {\[Mu], d}, {\[Nu], d}] /. truncate // Expand // Flatten // DeleteDuplicates
(
	lhs = Commutator[\[ScriptCapitalD], expSer] + \[CapitalDelta];
	rhs = (Sum[x[\[Mu]] D[expSer, x[\[Mu]]], {\[Mu], d}] + \[CapitalDelta]);
	lhs - rhs
) /. truncate // Expand


(* ::Subsection::Closed:: *)
(*General Ward identities*)


linearFun[name_] := (
	Clear[name];
	name[a___, b_ + c_, d___] := name[a, b, d] + name[a, c, d];
	name[a___, b_?NumericQ c_, d___] := b name[a, c, d];
);
linearFun[term1];
linearFun[term11];
linearFun[term12];


wardIdentity[A_, B_] := term11[A, B] - term12[B, A];


AntiCommutator[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[1]]
AntiCommutator[\[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[2]]


(* ::Text:: *)
(*Acting with one operator at point one gives*)


plusQ[\[ScriptCapitalQ]p[\[Alpha]_]|\[ScriptCapitalS]p[\[Alpha]d_]] := True
plusQ[_] := False
minusQ[\[ScriptCapitalQ]m[\[Alpha]d_]|\[ScriptCapitalS]m[\[Alpha]_]] := True
minusQ[_] := False


term1[\[ScriptCapitalD]] := Sum[x[1][\[Mu]] \[ScriptD][1][\[Mu]], {\[Mu], d}] + \[CapitalDelta]p id;
term1[\[ScriptCapitalR]] := 2 / (d-1) \[CapitalDelta]p id;
term1[\[ScriptCapitalP][\[Mu]_]] := \[ScriptD][1][\[Mu]];
term1[\[ScriptCapitalM][\[Mu]_, \[Nu]_]] := - (x[1][\[Mu]] \[ScriptD][1][\[Nu]] - x[1][\[Nu]] \[ScriptD][1][\[Mu]]);


term11[A_, A_] := 0;
term11[A_, B_?plusQ] = 0;
term11[A_?plusQ, B_] := term1[AntiCommutator[A, B]]
term11[\[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[1]] := -term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
term11[\[ScriptCapitalS]m[\[Alpha]_], A_] := Sum[x[1][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term11[\[ScriptCapitalQ]m[\[Alpha]d], A], {\[Mu], d}, {\[Alpha]d, 2}]


term12[A_, \[ScriptCapitalS]p[\[Alpha]d_]] := Sum[x[2][\[Mu]] \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[A, \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha], 2}]
term12[A_?plusQ, B_] := 0
term12[A_, B_?minusQ] := 0


applyOpBdy[terms_] := Module[{\[Xi]v, pref, restoreInv, expr},
	\[Xi]v = Sum[(x[1][\[Mu]] - x[2][\[Mu]])^2, {\[Mu], d}] / (4 x[1][d] x[2][d]);
	pref = (2 x[1][d])^(-\[CapitalDelta]p) (2 x[2][d])^(-\[CapitalDelta]p);
	restoreInv = Solve[\[Xi]v == \[Xi], x[1][1]] // First;
	expr = terms /. {
		\[ScriptD][i_][\[Mu]_] :> D[pref f[\[Xi]v], x[i][\[Mu]]],
		id :> pref f[\[Xi]v]
	};
	expr = (expr /. {\[Xi]v -> \[Xi]}) / pref // ExpandAll;
	expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &
]


(* ::Subsection::Closed:: *)
(*d=3: \[ScriptCapitalN]=(2,0) bulk channel*)


vars = Flatten @ Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}];
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First;
terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;
applyOpBdy[terms]


solWId


(* ::Subsection::Closed:: *)
(*d=3: \[ScriptCapitalN]=(1,1) bulk & bdy channel*)


vars = Flatten @ {
	Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}],
	term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
};
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[2] + \[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1] + \[ScriptCapitalS]m[2], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First;


(* ::Text:: *)
(*Defect channel*)


terms = (
	+ x[1][3] term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
	+ \[CapitalDelta]p id
) /. solWId;
applyOpBdy[terms]


(* ::Text:: *)
(*Bulk channel*)


terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;
applyOpBdy[terms]


(* ::Subsection::Closed:: *)
(*Twisted U(1) defect channel*)


Quit


(* ::Text:: *)
(*Non-supersymmetric blocks, with their equations and check they are solved*)


block\[Chi][\[CapitalDelta]_][\[Chi]_] := \[Chi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta]/2, (\[CapitalDelta]+1)/2, \[CapitalDelta]+1-1/2, 4/\[Chi]^2]
block\[Eta][s_][\[Eta]_] := Hypergeometric2F1[-s/2, s/2, 1/2, 1-\[Eta]^2]
block\[Eta]U1[r_, l_][\[Eta]_] := 1/2 ((\[Eta]-Sqrt[-1+\[Eta]^2])^-l +(\[Eta]-Sqrt[-1+\[Eta]^2])^(l+2r));
bosEq1 = (\[Chi]^2-4) f''[\[Chi]] + 2 \[Chi] f'[\[Chi]] - \[CapitalDelta](\[CapitalDelta]-1) f[\[Chi]];
bosEq2 = (\[Eta]^2-1) f''[\[Eta]] + \[Eta] f'[\[Eta]] - s^2 f[\[Eta]];
bosEq3 = (\[Eta]^2-1) f''[\[Eta]] + (\[Eta] + 2 r Sqrt[\[Eta]^2-1]) f'[\[Eta]] - l(l+2r) f[\[Eta]];

bosEq1 /. f -> block\[Chi][\[CapitalDelta]] // Series[#, {\[Chi], Infinity, 4}] &
bosEq2 /. f -> block\[Eta][s] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
bosEq3 /. f -> block\[Eta]U1[r, l] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &


(* ::Text:: *)
(*Full Casimir equation*)


casEq = (
	+ (1-\[Eta]^2) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- \[Eta] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (2\[CapitalDelta]p-1) Sqrt[\[Eta]^2-1] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (-1+\[CapitalDelta]p) \[CapitalDelta]p g[\[Eta], \[Chi]]
	+ (\[Chi]^2-4) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	+ 2 \[Chi] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (\[CapitalDelta]^2 - (\[CapitalDelta]p-1/2+l+1)^2) g[\[Eta], \[Chi]]
);
casEq /. g -> (block\[Chi][\[CapitalDelta]+1/2][#2] block\[Eta]U1[\[CapitalDelta]p-1/2, l+1][#1] &) // 
	Series[#, {\[Chi], Infinity, 10}, {\[Eta], 1, 10}] & // Simplify


(* ::Text:: *)
(*Possible solution for the \[Chi] part*)


diffEq = (
	+ (\[Chi]^2-4) f''[\[Chi]] 
	+ 2 \[Chi] f'[\[Chi]]
	- (\[CapitalDelta]^2 - 1/4) f[\[Chi]]
);
diffEq /. f -> block\[Chi][\[CapitalDelta]+1/2] // FullSimplify


DSolve[bosEq2 == 0, f[\[Eta]], \[Eta]] // FullSimplify


block\[Eta][s][\[Eta]] /. \[Eta] -> 1/2 (w + 1/w) // FullSimplify[#, w>1] &


Solve[1/2(w+1/w)==\[Eta], w]
1/2(w+1/w) /. % // Simplify


D[\[Eta]-Sqrt[-1+\[Eta]^2],\[Eta]] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
D[\[Eta]-Sqrt[-1+\[Eta]^2],{\[Eta],2}] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
\[Eta]^2-1 /. \[Eta] -> 1/2(w+1/w) // Together // Factor


\[Eta]-Sqrt[-1+\[Eta]^2] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ (\[Eta] + 2r Sqrt[\[Eta]^2-1]) f'[\[Eta]] 
	- l(l + 2r) f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


w^-l (w^(2l+2r) 1/2+1/2) // Expand
% /. w -> (\[Eta]-Sqrt[-1+\[Eta]^2]) // Simplify


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ \[Eta] f'[\[Eta]] 
	- l^2 f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


Cosh[1/2 l Log[w^2]]//FullSimplify[#, w>0] & // TrigToExp


(w^2)^(-a/2) % /. g -> (#^(a/2) h[#] &) // Collect[#, f_[w^2], Simplify] &


% /. a -> s


DSolve[-s^2 g[w2]+4 w2 g'[w2]+4 w2^2 g''[w2]==0, g[w2], w2]


block\[Eta][0][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][1][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][2][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][3][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &


Table[Cosh[1/2 s Log[w^2]] /. w -> \[Eta] -Sqrt[-1+\[Eta]^2], {s,0,5}] // Expand // FullSimplify[#, \[Eta]>1] &


DSolve[(1-s) Derivative[1][g][w2]+w2 (g^\[Prime]\[Prime])[w2] == 0, g[w2], w2]


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ (q-1) \[Eta] f'[\[Eta]]
	- s(s+q-2) f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, q/2-1, #] &) // FullSimplify


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- s^2 f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, #] &) // FullSimplify


Series[GegenbauerC[s, x], {x, 1, 5}]


diffEq /. f -> (g[(1-#)/2] &) /. \[Eta] -> 1 - 2\[Theta] // Simplify


GegenbauerC[n,x]


((-1+w^2)w^(s-2)/4 diffEq 
	/. f -> ((#-Sqrt[-1+#^2])^(-s) g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
)


Solve[{
	(-cas+s (-1+s+2 \[CapitalDelta]p)) == 0,
	a == 0,
	c == -(1/2) (-1) (-3+2 s+2 \[CapitalDelta]p),
	-(a+b+1) == -(1/2) (-3+2 s+2 \[CapitalDelta]p)
}, {cas, a, b, c}] // Simplify


Solve[\[Eta] == 1/2(w + 1/w), w]
% /. \[Eta] -> 1/2(w+1/w) // Simplify[#, w>0] &


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- (2\[CapitalDelta]p - 1) Sqrt[\[Eta]^2-1] f'[\[Eta]]
	- cas f[\[Eta]]
);
diffEq = diffEq //. {
	f -> (g[(#-Sqrt[-1+#^2])^2] &)
} /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 1>w>0] &


Solve[ (aa[1]+4 s aa[1]+aa[2]-4 s aa[2])==0, aa[1]] // Simplify


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]]


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]] // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2 (s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2 (s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2 (s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
cas->(aa[1]+4 s (aa[1]-aa[2])+aa[2]+4 s^2 (aa[0]+aa[1]+aa[2]))/(4 (aa[0]+aa[1]+aa[2])),
aa[0]->-(((1+2 s)^2 aa[1]+(1-2 s)^2 aa[2])/(4 s^2)),
aa[1]->((1-2 s)^2 (-1+4 s) aa[2])/((1+2 s)^2 (1+4 s)),
s -> 1/2
(*cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]\[Rule](-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]\[Rule]0 *)
} // Simplify // Series[#, {w, 1, 6}] &


(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])) //. {
(* cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[0]\[Rule](-aa[1]-4 s aa[1]-4 s^2 aa[1]-aa[2]+4 s aa[2]-4 s^2 aa[2])/(4 s^2),
aa[1]\[Rule](-aa[2]+8 s aa[2]-20 s^2 aa[2]+16 s^3 aa[2])/((1+2 s)^2 (1+4 s)) *)
cas->(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]->(-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]->0
} // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2(s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2(s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2(s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
} // Series[#, {w, 1, 5}] &


Hypergeometric2F1[0, -5/2+s+\[CapitalDelta]p,-3/2+s+\[CapitalDelta]p, w^2]


Solve[(-3+4 cas-8 s-4 s^2+4 \[CapitalDelta]p+8 s \[CapitalDelta]p)==0, cas] // Simplify


diffEq /. f -> (
	+ GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
&) /. {
	cas -> cas (* 1/4 (1+2 s) (3+2 s-4 \[CapitalDelta]p) *),
	aa[3]->-(((-1+2 s) (4 cas Cos[1/4 \[Pi] (1+2 s)]+(1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (3-2 s)]+(1+2 s) Sin[1/4 \[Pi] (5-2 s)])))/((1+2 s) (4 cas Sin[1/4 \[Pi] (3-2 s)]+(-1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (5-2 s)]+(-1+2 s) Sin[1/4 \[Pi] (7-2 s)]))))
} // Normal[Series[#, {\[Eta], 0, 2}], Assumptions-> \[Eta]>0] & // Expand // 
	Simplify[#, \[Eta]>0] & // Collect[#, \[Eta]^_, Factor] &


Solve[(-((4 cas Cos[1/4 \[Pi] (1+2 s)])/(1+2 s))+(2 I (1-2 \[CapitalDelta]p+s (-2+4 \[CapitalDelta]p)+2 I cas aa[3]) Sin[1/4 \[Pi] (3-2 s)])/(-1+2 s)-(1+2 s-2 I (-1+2 \[CapitalDelta]p) aa[3]) Sin[1/4 \[Pi] (5-2 s)]-(-1+2 s) aa[3] Sin[1/4 \[Pi] (7-2 s)])==0,aa[3]] // Simplify


diffEq /. f -> (GegenbauerC[s+1/2, #] &) // FullSimplify
Table[% /. {\[Eta] -> \[Eta]v, \[CapitalDelta]p -> 10, s -> 2}, {\[Eta]v, {1,2,5}}] // N


\[Eta]^s diffEq /. f -> (
	(* + aa[1] GegenbauerC[s, #] *)
	+ aa[2] GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
	(* + aa[4] GegenbauerC[s, #] *)
&) // Normal[Series[#, {\[Eta], Infinity, 2}]] & // Expand // Collect[#, \[Eta], Simplify] &


DSolve[diffEq == 0, f[\[Eta]], \[Eta]]


diffEq /. f -> block1[\[CapitalDelta]+1/2] // FullSimplify


eqs = (
	\[Chi]^\[CapitalDelta] diffEq /. ansatz 
	// Collect[#, HoldPattern[Hypergeometric2F1[___]], Simplify] &
	// Normal@Series[#, {\[Chi], Infinity, 5}] &
	// Collect[#, HoldPattern[Cos[___]|Sin[__]], Simplify] &
	// Normal@Series[#, {\[Eta], 0, 5}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
	// Expand // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &
);


Solve[(1+cas-\[CapitalDelta]^2-\[CapitalDelta]p)==0,cas]


eqs //. {
	s -> 1,
	aa[1] -> 0,
	aa[3]->(aa[2]+cas aa[2]-\[CapitalDelta]^2 aa[2]-\[CapitalDelta]p aa[2])/(1+cas-\[CapitalDelta]^2+3 \[CapitalDelta]p),
	cas->-1+\[CapitalDelta]^2+\[CapitalDelta]p,
	aa[2] -> 0
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


eqs //. {
	s -> 1/2,
	aa[1] -> 0,
	aa[3] -> 0,
	aa[4] -> 0,
	cas->-(1/4)+\[CapitalDelta]^2
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


(* ::Subsection::Closed:: *)
(*d=3: Line defect channel*)


Quit


(* ::Text:: *)
(*Non-supersymmetric blocks, with their equations and check they are solved*)


block\[Chi][\[CapitalDelta]_][\[Chi]_] := \[Chi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta]/2, (\[CapitalDelta]+1)/2, \[CapitalDelta]+1-1/2, 4/\[Chi]^2]
block\[Eta][s_][\[Eta]_] := Hypergeometric2F1[-s/2, s/2, 1/2, 1-\[Eta]^2]
block\[Eta]U1[r_, l_][\[Eta]_] := 1/2 ((\[Eta]-Sqrt[-1+\[Eta]^2])^-l +(\[Eta]-Sqrt[-1+\[Eta]^2])^(l+2r));
bosEq1 = (\[Chi]^2-4) f''[\[Chi]] + 2 \[Chi] f'[\[Chi]] - \[CapitalDelta](\[CapitalDelta]-1) f[\[Chi]];
bosEq2 = (\[Eta]^2-1) f''[\[Eta]] + \[Eta] f'[\[Eta]] - s^2 f[\[Eta]];
bosEq3 = (\[Eta]^2-1) f''[\[Eta]] + (\[Eta] + 2 r Sqrt[\[Eta]^2-1]) f'[\[Eta]] - l(l+2r) f[\[Eta]];

bosEq1 /. f -> block\[Chi][\[CapitalDelta]] // Series[#, {\[Chi], Infinity, 4}] &
bosEq2 /. f -> block\[Eta][s] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
bosEq3 /. f -> block\[Eta]U1[r, l] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &


(* ::Text:: *)
(*Full Casimir equation*)


casEq = (
	+ (1-\[Eta]^2) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- \[Eta] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (2\[CapitalDelta]p-1) Sqrt[\[Eta]^2-1] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (-1+\[CapitalDelta]p) \[CapitalDelta]p g[\[Eta], \[Chi]]
	+ (\[Chi]^2-4) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	+ 2 \[Chi] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (\[CapitalDelta]^2 - (\[CapitalDelta]p-1/2+l+1)^2) g[\[Eta], \[Chi]]
);
casEq /. g -> (block\[Chi][\[CapitalDelta]+1/2][#2] block\[Eta]U1[\[CapitalDelta]p-1/2, l+1][#1] &) // 
	Series[#, {\[Chi], Infinity, 10}, {\[Eta], 1, 10}] & // Simplify


(* ::Text:: *)
(*Possible solution for the \[Chi] part*)


diffEq = (
	+ (\[Chi]^2-4) f''[\[Chi]] 
	+ 2 \[Chi] f'[\[Chi]]
	- (\[CapitalDelta]^2 - 1/4) f[\[Chi]]
);
diffEq /. f -> block\[Chi][\[CapitalDelta]+1/2] // FullSimplify


DSolve[bosEq2 == 0, f[\[Eta]], \[Eta]] // FullSimplify


block\[Eta][s][\[Eta]] /. \[Eta] -> 1/2 (w + 1/w) // FullSimplify[#, w>1] &


Solve[1/2(w+1/w)==\[Eta], w]
1/2(w+1/w) /. % // Simplify


D[\[Eta]-Sqrt[-1+\[Eta]^2],\[Eta]] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
D[\[Eta]-Sqrt[-1+\[Eta]^2],{\[Eta],2}] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
\[Eta]^2-1 /. \[Eta] -> 1/2(w+1/w) // Together // Factor


\[Eta]-Sqrt[-1+\[Eta]^2] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ (\[Eta] + 2r Sqrt[\[Eta]^2-1]) f'[\[Eta]] 
	- l(l + 2r) f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


w^-l (w^(2l+2r) 1/2+1/2) // Expand
% /. w -> (\[Eta]-Sqrt[-1+\[Eta]^2]) // Simplify


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ \[Eta] f'[\[Eta]] 
	- l^2 f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


Cosh[1/2 l Log[w^2]]//FullSimplify[#, w>0] & // TrigToExp


(w^2)^(-a/2) % /. g -> (#^(a/2) h[#] &) // Collect[#, f_[w^2], Simplify] &


% /. a -> s


DSolve[-s^2 g[w2]+4 w2 g'[w2]+4 w2^2 g''[w2]==0, g[w2], w2]


block\[Eta][0][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][1][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][2][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][3][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &


Table[Cosh[1/2 s Log[w^2]] /. w -> \[Eta] -Sqrt[-1+\[Eta]^2], {s,0,5}] // Expand // FullSimplify[#, \[Eta]>1] &


DSolve[(1-s) Derivative[1][g][w2]+w2 (g^\[Prime]\[Prime])[w2] == 0, g[w2], w2]


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ (q-1) \[Eta] f'[\[Eta]]
	- s(s+q-2) f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, q/2-1, #] &) // FullSimplify


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- s^2 f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, #] &) // FullSimplify


Series[GegenbauerC[s, x], {x, 1, 5}]


diffEq /. f -> (g[(1-#)/2] &) /. \[Eta] -> 1 - 2\[Theta] // Simplify


GegenbauerC[n,x]


((-1+w^2)w^(s-2)/4 diffEq 
	/. f -> ((#-Sqrt[-1+#^2])^(-s) g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
)


Solve[{
	(-cas+s (-1+s+2 \[CapitalDelta]p)) == 0,
	a == 0,
	c == -(1/2) (-1) (-3+2 s+2 \[CapitalDelta]p),
	-(a+b+1) == -(1/2) (-3+2 s+2 \[CapitalDelta]p)
}, {cas, a, b, c}] // Simplify


Solve[\[Eta] == 1/2(w + 1/w), w]
% /. \[Eta] -> 1/2(w+1/w) // Simplify[#, w>0] &


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- (2\[CapitalDelta]p - 1) Sqrt[\[Eta]^2-1] f'[\[Eta]]
	- cas f[\[Eta]]
);
diffEq = diffEq //. {
	f -> (g[(#-Sqrt[-1+#^2])^2] &)
} /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 1>w>0] &


Solve[ (aa[1]+4 s aa[1]+aa[2]-4 s aa[2])==0, aa[1]] // Simplify


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]]


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]] // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2 (s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2 (s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2 (s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
cas->(aa[1]+4 s (aa[1]-aa[2])+aa[2]+4 s^2 (aa[0]+aa[1]+aa[2]))/(4 (aa[0]+aa[1]+aa[2])),
aa[0]->-(((1+2 s)^2 aa[1]+(1-2 s)^2 aa[2])/(4 s^2)),
aa[1]->((1-2 s)^2 (-1+4 s) aa[2])/((1+2 s)^2 (1+4 s)),
s -> 1/2
(*cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]\[Rule](-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]\[Rule]0 *)
} // Simplify // Series[#, {w, 1, 6}] &


(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])) //. {
(* cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[0]\[Rule](-aa[1]-4 s aa[1]-4 s^2 aa[1]-aa[2]+4 s aa[2]-4 s^2 aa[2])/(4 s^2),
aa[1]\[Rule](-aa[2]+8 s aa[2]-20 s^2 aa[2]+16 s^3 aa[2])/((1+2 s)^2 (1+4 s)) *)
cas->(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]->(-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]->0
} // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2(s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2(s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2(s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
} // Series[#, {w, 1, 5}] &


Hypergeometric2F1[0, -5/2+s+\[CapitalDelta]p,-3/2+s+\[CapitalDelta]p, w^2]


Solve[(-3+4 cas-8 s-4 s^2+4 \[CapitalDelta]p+8 s \[CapitalDelta]p)==0, cas] // Simplify


diffEq /. f -> (
	+ GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
&) /. {
	cas -> cas (* 1/4 (1+2 s) (3+2 s-4 \[CapitalDelta]p) *),
	aa[3]->-(((-1+2 s) (4 cas Cos[1/4 \[Pi] (1+2 s)]+(1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (3-2 s)]+(1+2 s) Sin[1/4 \[Pi] (5-2 s)])))/((1+2 s) (4 cas Sin[1/4 \[Pi] (3-2 s)]+(-1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (5-2 s)]+(-1+2 s) Sin[1/4 \[Pi] (7-2 s)]))))
} // Normal[Series[#, {\[Eta], 0, 2}], Assumptions-> \[Eta]>0] & // Expand // 
	Simplify[#, \[Eta]>0] & // Collect[#, \[Eta]^_, Factor] &


Solve[(-((4 cas Cos[1/4 \[Pi] (1+2 s)])/(1+2 s))+(2 I (1-2 \[CapitalDelta]p+s (-2+4 \[CapitalDelta]p)+2 I cas aa[3]) Sin[1/4 \[Pi] (3-2 s)])/(-1+2 s)-(1+2 s-2 I (-1+2 \[CapitalDelta]p) aa[3]) Sin[1/4 \[Pi] (5-2 s)]-(-1+2 s) aa[3] Sin[1/4 \[Pi] (7-2 s)])==0,aa[3]] // Simplify


diffEq /. f -> (GegenbauerC[s+1/2, #] &) // FullSimplify
Table[% /. {\[Eta] -> \[Eta]v, \[CapitalDelta]p -> 10, s -> 2}, {\[Eta]v, {1,2,5}}] // N


\[Eta]^s diffEq /. f -> (
	(* + aa[1] GegenbauerC[s, #] *)
	+ aa[2] GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
	(* + aa[4] GegenbauerC[s, #] *)
&) // Normal[Series[#, {\[Eta], Infinity, 2}]] & // Expand // Collect[#, \[Eta], Simplify] &


DSolve[diffEq == 0, f[\[Eta]], \[Eta]]


diffEq /. f -> block1[\[CapitalDelta]+1/2] // FullSimplify


eqs = (
	\[Chi]^\[CapitalDelta] diffEq /. ansatz 
	// Collect[#, HoldPattern[Hypergeometric2F1[___]], Simplify] &
	// Normal@Series[#, {\[Chi], Infinity, 5}] &
	// Collect[#, HoldPattern[Cos[___]|Sin[__]], Simplify] &
	// Normal@Series[#, {\[Eta], 0, 5}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
	// Expand // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &
);


Solve[(1+cas-\[CapitalDelta]^2-\[CapitalDelta]p)==0,cas]


eqs //. {
	s -> 1,
	aa[1] -> 0,
	aa[3]->(aa[2]+cas aa[2]-\[CapitalDelta]^2 aa[2]-\[CapitalDelta]p aa[2])/(1+cas-\[CapitalDelta]^2+3 \[CapitalDelta]p),
	cas->-1+\[CapitalDelta]^2+\[CapitalDelta]p,
	aa[2] -> 0
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


eqs //. {
	s -> 1/2,
	aa[1] -> 0,
	aa[3] -> 0,
	aa[4] -> 0,
	cas->-(1/4)+\[CapitalDelta]^2
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


(* ::Subsection::Closed:: *)
(*d=3: Line bulk channel*)


(* ::Subsubsection::Closed:: *)
(*Get contribution (now I get something else!!!)*)


vars = Flatten @ {
	Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}],
	term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
};
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First
terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;


(* ::Text:: *)
(*Bulk channel*)


Clear[x12Sq, x12Orth, x1Orth, x2Orth];
x12SqV = Sum[(x[1][\[Mu]] - x[2][\[Mu]])^2, {\[Mu], d}];
x1OrthV = Sqrt @ Sum[x[1][\[Mu]]^2, {\[Mu], d-1}];
x2OrthV = Sqrt @ Sum[x[2][\[Mu]]^2, {\[Mu], d-1}];
x12OrthV = Sum[x[1][\[Mu]] x[2][\[Mu]], {\[Mu], d-1}];
\[Xi]v = x12Sq / (x1Orth x2Orth);
\[Eta]v = x12Orth / (x1Orth x2Orth);
der[f_[\[Xi], \[Eta]], a_] := (
	+ D[f[\[Xi], \[Eta]], \[Xi]] der[\[Xi]v, a]
	+ D[f[\[Xi], \[Eta]], \[Eta]] der[\[Eta]v, a]
);
der[x12Sq, a_] := der[x12SqV, a];
der[x1Orth, a_] := der[x1OrthV, a];
der[x2Orth, a_] := der[x2OrthV, a];
der[x12Orth, a_] := der[x12OrthV, a];
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Delta][\[Mu], \[Nu]];
pref = x12Sq^(-\[CapitalDelta]p);
expr = terms /. {
	\[ScriptD][i_][\[Mu]_] :> der[pref f[\[Xi]v, \[Eta]v], x[i][\[Mu]]],
	id :> pref f[\[Xi]v, \[Eta]v]
};
expr = (expr /. {\[Xi]v -> \[Xi], \[Eta]v -> \[Eta]}) / pref // ExpandAll // Collect[#, f[\[Xi], \[Eta]], Simplify] &


restore\[Xi] = Solve[{
	\[Xi] x1Orth x2Orth == x12SqV
}, {x[1][3]}] // First;
expr2 = expr /. restore\[Xi] /. x12Sq -> \[Xi] x1Orth x2Orth // Collect[#, f[\[Xi], \[Eta]], Simplify] &


restore\[Eta] = Solve[{
	\[Eta] == x12OrthV / (x1OrthV x2OrthV),
	x[1][2] == 1,
	x[2][1] == 0
}, {x[1][1], x[1][2], x[2][1]}] // First;
expr3 = expr2 /. {x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. restore\[Eta] // 
	Simplify[#, x[2][2] > 0 && 1 < \[Eta] < 2] &


randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}
fs = {f[\[Xi], \[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]};
rr = randRules @@ (Flatten[Table[x[i][\[Mu]], {i, 2}, {\[Mu], 3}]]);
lhs = (Coefficient[expr, #] & /@ fs) /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
rhs = (Coefficient[expr3, #] & /@ fs) /. {\[Xi] -> \[Xi]v, \[Eta] -> \[Eta]v} /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
lhs - rhs


(* ::Subsubsection::Closed:: *)
(*Solve equation*)


bos = (
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
) /. {q -> 2};
susy = 1/Sqrt[-1+\[Eta]^2] (
	+(-1+\[Eta]^2) (2-2 \[Eta]^2+2 \[Eta] Sqrt[-1+\[Eta]^2]-\[Eta] \[Xi]+Sqrt[-1+\[Eta]^2] \[Xi]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
	+\[Xi] (-2 \[Eta]^3+2 Sqrt[-1+\[Eta]^2]+\[Eta]^2 (2 Sqrt[-1+\[Eta]^2]-\[Xi])+\[Xi]+\[Eta] (2+Sqrt[-1+\[Eta]^2] \[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
);
susy = (2 \[Eta]^3-2 Sqrt[-1+\[Eta]^2]-\[Xi]+\[Eta]^2 (2 Sqrt[-1+\[Eta]^2]+\[Xi])+\[Eta] (-2+Sqrt[-1+\[Eta]^2] \[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]+\[Xi] (2+2 \[Eta]^2+Sqrt[-1+\[Eta]^2] \[Xi]+\[Eta] (2 Sqrt[-1+\[Eta]^2]+\[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]];
{bos2, susy2} = ({bos, susy}
	/. f -> (f[- #1(#2 - I Sqrt[1-#2^2]), (#2 - I Sqrt[1-#2^2])^2] &) 
	/. {\[Xi] -> - u / Sqrt[v], \[Eta] -> (1+v) / (2Sqrt[v])} 
	/. {\[CapitalDelta][_] -> \[CapitalDelta]p, p -> d-2}
	 // Simplify[#, {u>0, v>1}] &
) // Collect[#, f_[u, v], Simplify] &


{bos3, susy3} = ({bos2, susy2}
	/. f -> (f[1/2 (1+#1-Sqrt[-4 #1+(1+#1-#2)^2]-#2),1/2 (1+#1+Sqrt[-4 #1+(1+#1-#2)^2]-#2)] &) 
	/. {u -> z zb, v -> (1-z)(1-zb)}
	// Simplify[#, zb>z] &
	// Collect[#, f_[z, zb], Simplify] &
)


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


bos3 /. f -> g2d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 2 /. randRules[\[CapitalDelta], l, z, zb]
bos3 /. f -> g4d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 4 /. randRules[\[CapitalDelta], l, z, zb]


{bos4, susy4} = ({bos3, susy3}
	/. f -> (f[#1/(1+Sqrt[1-#1])^2, #2/(1+Sqrt[1-#2])^2] &) 
	/. {z -> 4\[Rho] / (1+\[Rho])^2, zb -> 4\[Rho]b / (1+\[Rho]b)^2}
	// Simplify[#, 0<\[Rho]<1 && 0<\[Rho]b<1, TimeConstraint->1] &
	// Collect[#, f_[\[Rho], \[Rho]b], Simplify] &
)


(* ::Text:: *)
(*Equations in radial coordinates*)


{bos5, susy5} = ({bos4, susy4}
	/. f -> (f[(#1 #2)^(1/2), (#1 + #2)/(2 (#1 #2)^(1/2))] &) 
	/. {\[Rho]->r(\[Eta]+I Sqrt[1-\[Eta]^2]), \[Rho]b->r(\[Eta]-I Sqrt[1-\[Eta]^2])}
	// Simplify[#, 0<r && 0<\[Eta]<1, TimeConstraint->1] &
	// Collect[#, f_[r, \[Eta]], Simplify] &
)


(* ::Text:: *)
(*Check our recursion indeed works*)


maxL = 10;
maxOrd = 4;
blocks = cbRecurse[maxL, 0, 0, 3, maxOrd];
Table[blockFun[l] = Function[{r,\[Eta]}, Evaluate[blocks[[l+1]]]], {l, 0, maxL}];
Table[
	bos5 /. f -> blockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 3
, {l, 0, maxL}] // Series[#, {r, 0, maxOrd}] &


sblocks = Table[(
	+           blockFun[l+0][r, \[Eta]]
	+ (aa[l, 1] blockFun[l+1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 2] blockFun[l-1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 3] blockFun[l][r, \[Eta]]   /. \[CapitalDelta] -> \[CapitalDelta]+2)
), {l, maxL-1}];
Table[sblockFun[l] = Function[{r, \[Eta]}, Evaluate[sblocks[[l]]]], {l, maxL-1}];


sols = Table[
	expans = (4r)^-\[CapitalDelta] (bos5 + susy5) /. f -> sblockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d+2) + l(l+d-2) /. d -> 3;
	eqs = (
		Normal@Series[expans, {r, 0, maxOrd}] 
		// CoefficientList[#, {r, \[Eta]}] & 
		// Flatten // DeleteCases[#, 0] &
	);
	Solve[eqs == 0, {aa[l, 1], aa[l, 2], aa[l, 3]}] // Factor // First
, {l, maxL-1}]


a1 = FindSequenceFunction[Values @ sols[[;;,1]]][l] // Factor;
a2 = FindSequenceFunction[Values @ sols[[;;,2]]][l] // Factor;
a3 = FindSequenceFunction[Values @ sols[[;;,3]]][l] // Factor;


g[\[CapitalDelta],l] + a1 g[\[CapitalDelta]+1,l+1] + a2 g[\[CapitalDelta]+1,l-1]+ a3 g[\[CapitalDelta]+2,l] /. g[\[CapitalDelta]_,l_] :> Subscript[g, \[CapitalDelta],l] /. l -> \[ScriptL]


(* ::Subsection::Closed:: *)
(*d=4: OSp(1|4) bulk & bdy channel*)


vars = Flatten @ {
	Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}],
	term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
};
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1] + \[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[2] - \[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1] - \[ScriptCapitalS]m[2], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First;


(* ::Text:: *)
(*Defect channel*)


terms = (
	- I x[1][4] term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
	+ \[CapitalDelta]p id
) /. solWId;
applyOpBdy[terms]


(* ::Text:: *)
(*Bulk channel*)


terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;
applyOpBdy[terms]


(* ::Subsection::Closed:: *)
(*d=4: Surface defect channel*)


Quit


(* ::Text:: *)
(*Non-supersymmetric blocks, with their equations and check they are solved*)


block\[Chi][\[CapitalDelta]_][\[Chi]_] := \[Chi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta]/2, (\[CapitalDelta]+1)/2, \[CapitalDelta]+1-2/2, 4/\[Chi]^2]
block\[Eta][s_][\[Eta]_] := Hypergeometric2F1[-s/2, s/2, 1/2, 1-\[Eta]^2]
block\[Eta]U1[r_, l_][\[Eta]_] := 1/2 ((\[Eta]-Sqrt[-1+\[Eta]^2])^-l +(\[Eta]-Sqrt[-1+\[Eta]^2])^(l+2r));
bosEq1 = (\[Chi]^2-4) f''[\[Chi]] + 3 \[Chi] f'[\[Chi]] - \[CapitalDelta](\[CapitalDelta]-2) f[\[Chi]];
bosEq2 = (\[Eta]^2-1) f''[\[Eta]] + \[Eta] f'[\[Eta]] - s^2 f[\[Eta]];
bosEq3 = (\[Eta]^2-1) f''[\[Eta]] + (\[Eta] + 2 r Sqrt[\[Eta]^2-1]) f'[\[Eta]] - l(l+2r) f[\[Eta]];

bosEq1 /. f -> block\[Chi][\[CapitalDelta]] // Series[#, {\[Chi], Infinity, 4}] &
bosEq2 /. f -> block\[Eta][s] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
bosEq3 /. f -> block\[Eta]U1[r, l] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &


(* ::Text:: *)
(*Full Casimir equation*)


casEq = (
	+ (1-\[Eta]^2) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- \[Eta] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (2\[CapitalDelta]p-1) Sqrt[\[Eta]^2-1] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (-1+\[CapitalDelta]p) \[CapitalDelta]p g[\[Eta], \[Chi]]
	+ (\[Chi]^2-4) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	+ 3 \[Chi] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (\[CapitalDelta](\[CapitalDelta]-1) - (\[CapitalDelta]p-1/2+l+1)^2) g[\[Eta], \[Chi]]
);
casEq /. g -> (block\[Chi][\[CapitalDelta]+1/2][#2] block\[Eta]U1[\[CapitalDelta]p-1/2, l+1][#1] &) // 
	Series[#, {\[Chi], Infinity, 3}, {\[Eta], 1, 3}] &


(* ::Text:: *)
(*Possible solution for the \[Chi] part*)


diffEq = (
	+ (\[Chi]^2-4) f''[\[Chi]] 
	+ 3 \[Chi] f'[\[Chi]]
	- (\[CapitalDelta]+1/2)(\[CapitalDelta]+1/2-2) f[\[Chi]]
);
diffEq /. f -> block\[Chi][\[CapitalDelta]+1/2] // FullSimplify


DSolve[bosEq2 == 0, f[\[Eta]], \[Eta]] // FullSimplify


block\[Eta][s][\[Eta]] /. \[Eta] -> 1/2 (w + 1/w) // FullSimplify[#, w>1] &


Solve[1/2(w+1/w)==\[Eta], w]
1/2(w+1/w) /. % // Simplify


D[\[Eta]-Sqrt[-1+\[Eta]^2],\[Eta]] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
D[\[Eta]-Sqrt[-1+\[Eta]^2],{\[Eta],2}] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &
\[Eta]^2-1 /. \[Eta] -> 1/2(w+1/w) // Together // Factor


\[Eta]-Sqrt[-1+\[Eta]^2] /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 0<w<1] &


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ (\[Eta] + 2r Sqrt[\[Eta]^2-1]) f'[\[Eta]] 
	- l(l + 2r) f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


w^-l (w^(2l+2r) 1/2+1/2) // Expand
% /. w -> (\[Eta]-Sqrt[-1+\[Eta]^2]) // Simplify


bosEq = (
	+ (\[Eta]^2-1) f''[\[Eta]]
	+ \[Eta] f'[\[Eta]] 
	- l^2 f[\[Eta]]
);
( bosEq /. f -> (g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
) /. w -> Sqrt@w2
DSolve[% == 0, g[w2], w2] // FullSimplify[#, l>r>0] &


Cosh[1/2 l Log[w^2]]//FullSimplify[#, w>0] & // TrigToExp


(w^2)^(-a/2) % /. g -> (#^(a/2) h[#] &) // Collect[#, f_[w^2], Simplify] &


% /. a -> s


DSolve[-s^2 g[w2]+4 w2 g'[w2]+4 w2^2 g''[w2]==0, g[w2], w2]


block\[Eta][0][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][1][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][2][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &
block\[Eta][3][\[Eta]] /. \[Eta] -> 1/2(w+1/w) // Simplify[#, 1>w>0] &


Table[Cosh[1/2 s Log[w^2]] /. w -> \[Eta] -Sqrt[-1+\[Eta]^2], {s,0,5}] // Expand // FullSimplify[#, \[Eta]>1] &


DSolve[(1-s) Derivative[1][g][w2]+w2 (g^\[Prime]\[Prime])[w2] == 0, g[w2], w2]


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ (q-1) \[Eta] f'[\[Eta]]
	- s(s+q-2) f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, q/2-1, #] &) // FullSimplify


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- s^2 f[\[Eta]]
);
diffEq /. f -> (GegenbauerC[s, #] &) // FullSimplify


Series[GegenbauerC[s, x], {x, 1, 5}]


diffEq /. f -> (g[(1-#)/2] &) /. \[Eta] -> 1 - 2\[Theta] // Simplify


GegenbauerC[n,x]


((-1+w^2)w^(s-2)/4 diffEq 
	/. f -> ((#-Sqrt[-1+#^2])^(-s) g[(#-Sqrt[-1+#^2])^2] &) 
	/. \[Eta] -> 1/2(w+1/w) 
	// FullSimplify[#, 1>w>0] &
	// Collect[#, f_[w^2], Simplify] &
)


Solve[{
	(-cas+s (-1+s+2 \[CapitalDelta]p)) == 0,
	a == 0,
	c == -(1/2) (-1) (-3+2 s+2 \[CapitalDelta]p),
	-(a+b+1) == -(1/2) (-3+2 s+2 \[CapitalDelta]p)
}, {cas, a, b, c}] // Simplify


Solve[\[Eta] == 1/2(w + 1/w), w]
% /. \[Eta] -> 1/2(w+1/w) // Simplify[#, w>0] &


diffEq = (
	+ (\[Eta]^2-1) f''[\[Eta]] 
	+ \[Eta] f'[\[Eta]]
	- (2\[CapitalDelta]p - 1) Sqrt[\[Eta]^2-1] f'[\[Eta]]
	- cas f[\[Eta]]
);
diffEq = diffEq //. {
	f -> (g[(#-Sqrt[-1+#^2])^2] &)
} /. \[Eta] -> 1/2(w+1/w) // FullSimplify[#, 1>w>0] &


Solve[ (aa[1]+4 s aa[1]+aa[2]-4 s aa[2])==0, aa[1]] // Simplify


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]]


Solve[(aa[1]+8 s aa[1]+20 s^2 aa[1]+16 s^3 aa[1]+aa[2]-8 s aa[2]+20 s^2 aa[2]-16 s^3 aa[2])==0, aa[1]] // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2 (s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2 (s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2 (s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
cas->(aa[1]+4 s (aa[1]-aa[2])+aa[2]+4 s^2 (aa[0]+aa[1]+aa[2]))/(4 (aa[0]+aa[1]+aa[2])),
aa[0]->-(((1+2 s)^2 aa[1]+(1-2 s)^2 aa[2])/(4 s^2)),
aa[1]->((1-2 s)^2 (-1+4 s) aa[2])/((1+2 s)^2 (1+4 s)),
s -> 1/2
(*cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]\[Rule](-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]\[Rule]0 *)
} // Simplify // Series[#, {w, 1, 6}] &


(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])) //. {
(* cas\[Rule](4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[0]\[Rule](-aa[1]-4 s aa[1]-4 s^2 aa[1]-aa[2]+4 s aa[2]-4 s^2 aa[2])/(4 s^2),
aa[1]\[Rule](-aa[2]+8 s aa[2]-20 s^2 aa[2]+16 s^3 aa[2])/((1+2 s)^2 (1+4 s)) *)
cas->(4 s^2 aa[0]+aa[1]+4 s aa[1]+4 s^2 aa[1]+aa[2]-4 s aa[2]+4 s^2 aa[2])/(4 (aa[0]+aa[1]+aa[2])),
aa[1]->(-aa[0] aa[2]+8 s aa[0] aa[2]-16 s^2 aa[0] aa[2])/(aa[0]+8 s aa[0]+16 s^2 aa[0]+64 s^2 aa[2]),
aa[2]->0
} // Simplify


diffEq /. {g -> (
	+ aa[0] Cosh[1/2(s + 0/2) Log[#]]
	+ aa[1] Cosh[1/2(s + 1/2) Log[#]]
	+ aa[2] Cosh[1/2(s - 1/2) Log[#]]
	(* + aa[3] Cosh[(s + 0/2) Log[#]] *)
&)} //. {
} // Series[#, {w, 1, 5}] &


Hypergeometric2F1[0, -5/2+s+\[CapitalDelta]p,-3/2+s+\[CapitalDelta]p, w^2]


Solve[(-3+4 cas-8 s-4 s^2+4 \[CapitalDelta]p+8 s \[CapitalDelta]p)==0, cas] // Simplify


diffEq /. f -> (
	+ GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
&) /. {
	cas -> cas (* 1/4 (1+2 s) (3+2 s-4 \[CapitalDelta]p) *),
	aa[3]->-(((-1+2 s) (4 cas Cos[1/4 \[Pi] (1+2 s)]+(1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (3-2 s)]+(1+2 s) Sin[1/4 \[Pi] (5-2 s)])))/((1+2 s) (4 cas Sin[1/4 \[Pi] (3-2 s)]+(-1+2 s) (-2 I (-1+2 \[CapitalDelta]p) Sin[1/4 \[Pi] (5-2 s)]+(-1+2 s) Sin[1/4 \[Pi] (7-2 s)]))))
} // Normal[Series[#, {\[Eta], 0, 2}], Assumptions-> \[Eta]>0] & // Expand // 
	Simplify[#, \[Eta]>0] & // Collect[#, \[Eta]^_, Factor] &


Solve[(-((4 cas Cos[1/4 \[Pi] (1+2 s)])/(1+2 s))+(2 I (1-2 \[CapitalDelta]p+s (-2+4 \[CapitalDelta]p)+2 I cas aa[3]) Sin[1/4 \[Pi] (3-2 s)])/(-1+2 s)-(1+2 s-2 I (-1+2 \[CapitalDelta]p) aa[3]) Sin[1/4 \[Pi] (5-2 s)]-(-1+2 s) aa[3] Sin[1/4 \[Pi] (7-2 s)])==0,aa[3]] // Simplify


diffEq /. f -> (GegenbauerC[s+1/2, #] &) // FullSimplify
Table[% /. {\[Eta] -> \[Eta]v, \[CapitalDelta]p -> 10, s -> 2}, {\[Eta]v, {1,2,5}}] // N


\[Eta]^s diffEq /. f -> (
	(* + aa[1] GegenbauerC[s, #] *)
	+ aa[2] GegenbauerC[s+1/2, #] 
	+ aa[3] GegenbauerC[s-1/2, #] 
	(* + aa[4] GegenbauerC[s, #] *)
&) // Normal[Series[#, {\[Eta], Infinity, 2}]] & // Expand // Collect[#, \[Eta], Simplify] &


DSolve[diffEq == 0, f[\[Eta]], \[Eta]]


diffEq /. f -> block1[\[CapitalDelta]+1/2] // FullSimplify


eqs = (
	\[Chi]^\[CapitalDelta] diffEq /. ansatz 
	// Collect[#, HoldPattern[Hypergeometric2F1[___]], Simplify] &
	// Normal@Series[#, {\[Chi], Infinity, 5}] &
	// Collect[#, HoldPattern[Cos[___]|Sin[__]], Simplify] &
	// Normal@Series[#, {\[Eta], 0, 5}, Assumptions-> 0<\[Eta] && \[Eta]<1] &
	// Expand // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &
);


Solve[(1+cas-\[CapitalDelta]^2-\[CapitalDelta]p)==0,cas]


eqs //. {
	s -> 1,
	aa[1] -> 0,
	aa[3]->(aa[2]+cas aa[2]-\[CapitalDelta]^2 aa[2]-\[CapitalDelta]p aa[2])/(1+cas-\[CapitalDelta]^2+3 \[CapitalDelta]p),
	cas->-1+\[CapitalDelta]^2+\[CapitalDelta]p,
	aa[2] -> 0
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


eqs //. {
	s -> 1/2,
	aa[1] -> 0,
	aa[3] -> 0,
	aa[4] -> 0,
	cas->-(1/4)+\[CapitalDelta]^2
} // Collect[#, \[Chi], Collect[#, \[Eta], Factor] &] &


(* ::Subsection::Closed:: *)
(*d=4: Surface bulk channel*)


(* ::Subsubsection::Closed:: *)
(*Get contribution*)


vars = Flatten @ {
	Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}],
	term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
};
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First
terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;


(* ::Text:: *)
(*Bulk channel*)


Clear[x12Sq, x12Orth, x1Orth, x2Orth];
x12SqV = Sum[(x[1][\[Mu]] - x[2][\[Mu]])^2, {\[Mu], d}];
x1OrthV = Sqrt @ Sum[x[1][\[Mu]]^2, {\[Mu], d-2}];
x2OrthV = Sqrt @ Sum[x[2][\[Mu]]^2, {\[Mu], d-2}];
x12OrthV = Sum[x[1][\[Mu]] x[2][\[Mu]], {\[Mu], d-2}];
\[Xi]v = x12Sq / (x1Orth x2Orth);
\[Eta]v = x12Orth / (x1Orth x2Orth);
der[f_[\[Xi], \[Eta]], a_] := (
	+ D[f[\[Xi], \[Eta]], \[Xi]] der[\[Xi]v, a]
	+ D[f[\[Xi], \[Eta]], \[Eta]] der[\[Eta]v, a]
);
der[x12Sq, a_] := der[x12SqV, a];
der[x1Orth, a_] := der[x1OrthV, a];
der[x2Orth, a_] := der[x2OrthV, a];
der[x12Orth, a_] := der[x12OrthV, a];
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Delta][\[Mu], \[Nu]];
pref = x12Sq^(-\[CapitalDelta]p);
expr = terms /. {
	\[ScriptD][i_][\[Mu]_] :> der[pref f[\[Xi]v, \[Eta]v], x[i][\[Mu]]],
	id :> pref f[\[Xi]v, \[Eta]v]
};
expr = (expr /. {\[Xi]v -> \[Xi], \[Eta]v -> \[Eta]}) / pref // ExpandAll // Collect[#, f[\[Xi], \[Eta]], Simplify] &


restore\[Xi] = Solve[{
	\[Xi] x1Orth x2Orth == x12SqV
}, {x[1][4]}] // First
expr2 = expr /. restore\[Xi] /. x12Sq -> \[Xi] x1Orth x2Orth // Collect[#, f[\[Xi], \[Eta]], Simplify] &


restore\[Eta] = Solve[{
	\[Eta] == x12OrthV / (x1OrthV x2OrthV),
	x[1][2] == 1,
	x[2][1] == 0
}, {x[1][1], x[1][2], x[2][1]}] // First;
expr3 = expr2 /. {x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. restore\[Eta] // 
	Simplify[#, x[2][2] > 0 && 1 < \[Eta] < 2] &


randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}
fs = {f[\[Xi], \[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]};
rr = randRules @@ (Flatten[Table[x[i][\[Mu]], {i, 2}, {\[Mu], d}]]);
lhs = (Coefficient[expr, #] & /@ fs) /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
rhs = (Coefficient[expr3, #] & /@ fs) /. {\[Xi] -> \[Xi]v, \[Eta] -> \[Eta]v} /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
lhs - rhs // Expand


(* ::Subsubsection::Closed:: *)
(*Solve equation*)


bos = (
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
) /. {q -> 2};
susy = (
	+ (2 \[Eta]^3-2 Sqrt[-1+\[Eta]^2]-\[Xi]+\[Eta]^2 (2 Sqrt[-1+\[Eta]^2]+\[Xi])+\[Eta] (-2+Sqrt[-1+\[Eta]^2] \[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
	+\[Xi] (2+2 \[Eta]^2+Sqrt[-1+\[Eta]^2] \[Xi]+\[Eta] (2 Sqrt[-1+\[Eta]^2]+\[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
);
{bos2, susy2} = ({bos, susy}
	/. f -> (f[- #1(#2 - I Sqrt[1-#2^2]), (#2 - I Sqrt[1-#2^2])^2] &) 
	/. {\[Xi] -> - u / Sqrt[v], \[Eta] -> (1+v) / (2Sqrt[v])} 
	/. {\[CapitalDelta][_] -> \[CapitalDelta]p, p -> d-2}
	 // Simplify[#, {u>0, v>1}] &
) // Collect[#, f_[u, v], Simplify] &


{bos3, susy3} = ({bos2, susy2}
	/. f -> (f[1/2 (1+#1-Sqrt[-4 #1+(1+#1-#2)^2]-#2),1/2 (1+#1+Sqrt[-4 #1+(1+#1-#2)^2]-#2)] &) 
	/. {u -> z zb, v -> (1-z)(1-zb)}
	// Simplify[#, zb>z] &
	// Collect[#, f_[z, zb], Simplify] &
)


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


bos3 /. f -> g2d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 2 /. randRules[\[CapitalDelta], l, z, zb]
bos3 /. f -> g4d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 4 /. randRules[\[CapitalDelta], l, z, zb]


{bos4, susy4} = ({bos3, susy3}
	/. f -> (f[#1/(1+Sqrt[1-#1])^2, #2/(1+Sqrt[1-#2])^2] &) 
	/. {z -> 4\[Rho] / (1+\[Rho])^2, zb -> 4\[Rho]b / (1+\[Rho]b)^2}
	// Simplify[#, 0<\[Rho]<1 && 0<\[Rho]b<1, TimeConstraint->1] &
	// Collect[#, f_[\[Rho], \[Rho]b], Simplify] &
)


(* ::Text:: *)
(*Equations in radial coordinates*)


{bos5, susy5} = ({bos4, susy4}
	/. f -> (f[(#1 #2)^(1/2), (#1 + #2)/(2 (#1 #2)^(1/2))] &) 
	/. {\[Rho]->r(\[Eta]+I Sqrt[1-\[Eta]^2]), \[Rho]b->r(\[Eta]-I Sqrt[1-\[Eta]^2])}
	// Simplify[#, 0<r && 0<\[Eta]<1, TimeConstraint->1] &
	// Collect[#, f_[r, \[Eta]], Simplify] &
)


(* ::Text:: *)
(*Check our recursion indeed works*)


maxL = 10;
maxOrd = 4;
blocks = cbRecurse[maxL, 0, 0, 3, maxOrd];
Table[blockFun[l] = Function[{r,\[Eta]}, Evaluate[blocks[[l+1]]]], {l, 0, maxL}];
Table[
	bos5 /. f -> blockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 3
, {l, 0, maxL}] // Series[#, {r, 0, maxOrd}] &


sblocks = Table[(
	+           blockFun[l+0][r, \[Eta]]
	+ (aa[l, 1] blockFun[l+1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 2] blockFun[l-1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 3] blockFun[l][r, \[Eta]]   /. \[CapitalDelta] -> \[CapitalDelta]+2)
), {l, maxL-1}];
Table[sblockFun[l] = Function[{r, \[Eta]}, Evaluate[sblocks[[l]]]], {l, maxL-1}];


sols = Table[
	expans = (4r)^-\[CapitalDelta] (bos5 + susy5) /. f -> sblockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d+2) + l(l+d-2) /. d -> 3;
	eqs = (
		Normal@Series[expans, {r, 0, maxOrd}] 
		// CoefficientList[#, {r, \[Eta]}] & 
		// Flatten // DeleteCases[#, 0] &
	);
	Solve[eqs == 0, {aa[l, 1], aa[l, 2], aa[l, 3]}] // Factor // First
, {l, maxL-1}]


a1 = FindSequenceFunction[Values @ sols[[;;,1]]][l] // Factor;
a2 = FindSequenceFunction[Values @ sols[[;;,2]]][l] // Factor;
a3 = FindSequenceFunction[Values @ sols[[;;,3]]][l] // Factor;


g[\[CapitalDelta],l] + a1 g[\[CapitalDelta]+1,l+1] + a2 g[\[CapitalDelta]+1,l-1]+ a3 g[\[CapitalDelta]+2,l] /. g[\[CapitalDelta]_,l_] :> Subscript[g, \[CapitalDelta],l] /. l -> \[ScriptL]


(* ::Subsection::Closed:: *)
(*d=4: Surface bulk channel (old)*)


(* ::Subsubsection:: *)
(*Get contribution*)


vars = Flatten @ {
	Table[term12[\[ScriptCapitalQ]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}],
	term11[\[ScriptCapitalQ]m[1], \[ScriptCapitalQ]m[2]]
};
solWId = Solve[{
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]p[1], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalQ]m[2], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]p[2], \[ScriptCapitalQ]m[2]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[1]] == 0,
	wardIdentity[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]m[2]] == 0
}, vars] // First
terms = (
	+ Sum[(x[1][\[Mu]] - x[2][\[Mu]]) \[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] term12[\[ScriptCapitalQ]m[\[Alpha]d], \[ScriptCapitalQ]p[\[Alpha]]], {\[Mu], d}, {\[Alpha],  2}, {\[Alpha]d, 2}]
	+ 4 \[CapitalDelta]p id
) /. solWId;


(* ::Text:: *)
(*Bulk channel*)


Clear[x12Sq, x12Orth, x1Orth, x2Orth];
x12SqV = Sum[(x[1][\[Mu]] - x[2][\[Mu]])^2, {\[Mu], d}];
x1OrthV = Sqrt @ Sum[x[1][\[Mu]]^2, {\[Mu], d-2}];
x2OrthV = Sqrt @ Sum[x[2][\[Mu]]^2, {\[Mu], d-2}];
x12OrthV = Sum[x[1][\[Mu]] x[2][\[Mu]], {\[Mu], d-2}];
\[Xi]v = x12Sq / (x1Orth x2Orth);
\[Eta]v = x12Orth / (x1Orth x2Orth);
der[f_[\[Xi], \[Eta]], a_] := (
	+ D[f[\[Xi], \[Eta]], \[Xi]] der[\[Xi]v, a]
	+ D[f[\[Xi], \[Eta]], \[Eta]] der[\[Eta]v, a]
);
der[x12Sq, a_] := der[x12SqV, a];
der[x1Orth, a_] := der[x1OrthV, a];
der[x2Orth, a_] := der[x2OrthV, a];
der[x12Orth, a_] := der[x12OrthV, a];
der[x[i_][\[Mu]_], x[j_][\[Nu]_]] := \[Delta][i, j] \[Delta][\[Mu], \[Nu]];
pref = x12Sq^(-\[CapitalDelta]p);
expr = terms /. {
	\[ScriptD][i_][\[Mu]_] :> der[pref f[\[Xi]v, \[Eta]v], x[i][\[Mu]]],
	id :> pref f[\[Xi]v, \[Eta]v]
};
expr = (expr /. {\[Xi]v -> \[Xi], \[Eta]v -> \[Eta]}) / pref // ExpandAll // Collect[#, f[\[Xi], \[Eta]], Simplify] &


restore\[Xi] = Solve[{
	\[Xi] x1Orth x2Orth == x12SqV
}, {x[1][4]}] // First
expr2 = expr /. restore\[Xi] /. x12Sq -> \[Xi] x1Orth x2Orth // Collect[#, f[\[Xi], \[Eta]], Simplify] &


x12OrthV / (x1OrthV x2OrthV)


restore\[Eta] = Solve[{
	\[Eta] == x12OrthV / (x1OrthV x2OrthV),
	x[1][2] == 1,
	x[2][1] == 0
}, {x[1][1], x[1][2], x[2][1]}] // First


expr3 = expr2 /. {x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. restore\[Eta] // 
	Simplify[#, x[2][2] > 0 && 1 < \[Eta] < 2] &


randRules[args__] := (# -> RandomReal[WorkingPrecision->200]) & /@ {args}


fs = {f[\[Xi], \[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]], \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]};


rr = randRules @@ (Flatten[Table[x[i][\[Mu]], {i, 2}, {\[Mu], 3}]]);
lhs = (Coefficient[expr, #] & /@ fs) /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
rhs = (Coefficient[expr3, #] & /@ fs) /. {\[Xi] -> \[Xi]v, \[Eta] -> \[Eta]v} /. {x12Sq -> x12SqV, x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV} /. rr;
lhs // Expand
rhs // Expand
% - %%


\[Eta]V = \[Eta]v /. {x12Orth -> x12OrthV, x1Orth -> x1OrthV, x2Orth -> x2OrthV}


(-I x[1][2] x[2][1]+I x[1][1] x[2][2])


{\[Eta]V, 1 - \[Eta]V^2} // Together // Factor
% /. {
	x[1][1] x[2][1] -> \[Eta] x1Orth x2Orth - x[1][2] x[2][2],
	x[1][1] x[2][2] -> Sqrt[1-\[Eta]^2] x1Orth x2Orth + x[1][2] x[2][1]
} // Simplify



expr3 = expr2 //. {
	(x[2][1]-I x[2][2]) -> x2Orth^2 / (x[2][1]+I x[2][2]),
	(x[1][1]^2+x[1][2]^2)^a_ :> x1Orth^(2a),
	x12Sq -> \[Xi] x1Orth x2Orth
} // Collect[#, f_[\[Xi], \[Eta]], Collect[#, \[Xi], ExpandNumerator@*Together] &] &


expr4 = expr3 //. {
	x[1][1] x[2][1] -> \[Eta] x1Orth x2Orth - x[1][2] x[2][2],
	x[1][1] x[2][2] -> Sqrt[1-\[Eta]^2] x1Orth x2Orth + x[1][2] x[2][1],
	x12Orth -> \[Eta] x1Orth x2Orth
} // Collect[#, f_[\[Xi], \[Eta]], Collect[#, \[Xi], ExpandNumerator@*Together] &] &


\[Eta]V


restore\[Eta] = Solve[{
	\[Eta]V == \[Eta],
	x[1][2] == 1,
	x[2][2] == 0
}, {x[1][1], x[1][2], x[2][2]}] // First


expr4 //. {
	x[1][1] x[2][1] -> \[Eta] x1Orth x2Orth - x[1][2] x[2][2],
	x[1][1] x[2][2] -> Sqrt[1-\[Eta]^2] x1Orth x2Orth + x[1][2] x[2][1],
	x12Orth -> \[Eta] x1Orth x2Orth
} // Collect[#, f_[\[Xi], \[Eta]], Collect[#, \[Xi], ExpandNumerator@*Together] &] &


(x[2][1]+I x[2][2]) (x[1][1]-I (x[1][2]+I x[2][1]+x[2][2])) // Expand


cc = (x[2][1]+I x[2][2]);
cc ExpandDenominator[Expand[expr2 / cc]] // Collect[#, f[\[Xi], \[Eta]], Factor@*Combine@*ExpandAll] &


restoreInv = Solve[\[Xi]v == \[Xi], x[1][1]] // First;
expr = (expr /. {\[Xi]v -> \[Xi]}) / pref // ExpandAll;
expr /. restoreInv // Collect[#, f_[\[Xi]], Factor] &



applyOpBdy[terms]


(* ::Subsubsection::Closed:: *)
(*Solve equation*)


bos = (
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
) /. {q -> 2};
susy = 1/Sqrt[-1+\[Eta]^2] (
	+(-1+\[Eta]^2) (2-2 \[Eta]^2+2 \[Eta] Sqrt[-1+\[Eta]^2]-\[Eta] \[Xi]+Sqrt[-1+\[Eta]^2] \[Xi]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
	+\[Xi] (-2 \[Eta]^3+2 Sqrt[-1+\[Eta]^2]+\[Eta]^2 (2 Sqrt[-1+\[Eta]^2]-\[Xi])+\[Xi]+\[Eta] (2+Sqrt[-1+\[Eta]^2] \[Xi])) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Xi],\[Eta]]
);
{bos2, susy2} = ({bos, susy}
	/. f -> (f[- #1(#2 - I Sqrt[1-#2^2]), (#2 - I Sqrt[1-#2^2])^2] &) 
	/. {\[Xi] -> - u / Sqrt[v], \[Eta] -> (1+v) / (2Sqrt[v])} 
	/. {\[CapitalDelta][_] -> \[CapitalDelta]p, p -> d-2}
	 // Simplify[#, {u>0, v>1}] &
) // Collect[#, f_[u, v], Simplify] &


{bos3, susy3} = ({bos2, susy2}
	/. f -> (f[1/2 (1+#1-Sqrt[-4 #1+(1+#1-#2)^2]-#2),1/2 (1+#1+Sqrt[-4 #1+(1+#1-#2)^2]-#2)] &) 
	/. {u -> z zb, v -> (1-z)(1-zb)}
	// Simplify[#, zb>z] &
	// Collect[#, f_[z, zb], Simplify] &
)


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


bos3 /. f -> g2d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 2 /. randRules[\[CapitalDelta], l, z, zb]
bos3 /. f -> g4d[\[CapitalDelta], l, 0, 0] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 4 /. randRules[\[CapitalDelta], l, z, zb]


{bos4, susy4} = ({bos3, susy3}
	/. f -> (f[#1/(1+Sqrt[1-#1])^2, #2/(1+Sqrt[1-#2])^2] &) 
	/. {z -> 4\[Rho] / (1+\[Rho])^2, zb -> 4\[Rho]b / (1+\[Rho]b)^2}
	// Simplify[#, 0<\[Rho]<1 && 0<\[Rho]b<1, TimeConstraint->1] &
	// Collect[#, f_[\[Rho], \[Rho]b], Simplify] &
)


(* ::Text:: *)
(*Equations in radial coordinates*)


{bos5, susy5} = ({bos4, susy4}
	/. f -> (f[(#1 #2)^(1/2), (#1 + #2)/(2 (#1 #2)^(1/2))] &) 
	/. {\[Rho]->r(\[Eta]+I Sqrt[1-\[Eta]^2]), \[Rho]b->r(\[Eta]-I Sqrt[1-\[Eta]^2])}
	// Simplify[#, 0<r && 0<\[Eta]<1, TimeConstraint->1] &
	// Collect[#, f_[r, \[Eta]], Simplify] &
)


(* ::Text:: *)
(*Check our recursion indeed works*)


maxL = 10;
maxOrd = 4;
blocks = cbRecurse[maxL, 0, 0, 3, maxOrd];
Table[blockFun[l] = Function[{r,\[Eta]}, Evaluate[blocks[[l+1]]]], {l, 0, maxL}];
Table[
	bos5 /. f -> blockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d) + l(l+d-2) /. d -> 3
, {l, 0, maxL}] // Series[#, {r, 0, maxOrd}] &


sblocks = Table[(
	+           blockFun[l+0][r, \[Eta]]
	+ (aa[l, 1] blockFun[l+1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 2] blockFun[l-1][r, \[Eta]] /. \[CapitalDelta] -> \[CapitalDelta]+1)
	+ (aa[l, 3] blockFun[l][r, \[Eta]]   /. \[CapitalDelta] -> \[CapitalDelta]+2)
), {l, maxL-1}];
Table[sblockFun[l] = Function[{r, \[Eta]}, Evaluate[sblocks[[l]]]], {l, maxL-1}];


sols = Table[
	expans = (4r)^-\[CapitalDelta] (bos5 + susy5) /. f -> sblockFun[l] /. cas -> \[CapitalDelta](\[CapitalDelta]-d+2) + l(l+d-2) /. d -> 3;
	eqs = (
		Normal@Series[expans, {r, 0, maxOrd}] 
		// CoefficientList[#, {r, \[Eta]}] & 
		// Flatten // DeleteCases[#, 0] &
	);
	Solve[eqs == 0, {aa[l, 1], aa[l, 2], aa[l, 3]}] // Factor // First
, {l, maxL-1}]


a1 = FindSequenceFunction[Values @ sols[[;;,1]]][l] // Factor;
a2 = FindSequenceFunction[Values @ sols[[;;,2]]][l] // Factor;
a3 = FindSequenceFunction[Values @ sols[[;;,3]]][l] // Factor;


g[\[CapitalDelta],l] + a1 g[\[CapitalDelta]+1,l+1] + a2 g[\[CapitalDelta]+1,l-1]+ a3 g[\[CapitalDelta]+2,l] /. g[\[CapitalDelta]_,l_] :> Subscript[g, \[CapitalDelta],l] /. l -> \[ScriptL]


(* ::Section:: *)
(*Superspace*)


(* ::Subsection::Closed:: *)
(*Obtain differential operators*)


Boson[\[ScriptX][_], d\[ScriptX][_]];
Fermion[\[Theta]p[_], d\[Theta]p[_], \[Theta]m[_], d\[Theta]m[_]];
Table[SetCommutator[d\[ScriptX][\[Mu]], \[ScriptX][\[Mu]], 1], {\[Mu], d}];
Table[{
	SetAntiCommutator[d\[Theta]p[\[Alpha]], \[Theta]p[\[Alpha]], 1],
	SetAntiCommutator[d\[Theta]m[\[Alpha]], \[Theta]m[\[Alpha]], 1]
}, {\[Alpha], 2}];
SetOrder[{\[ScriptX][_], \[Theta]p[_], \[Theta]m[_]}, 1];
SetOrder[{\[ScriptCapitalD], \[ScriptCapitalP][_], \[ScriptCapitalK][_], \[ScriptCapitalM][_, _], \[ScriptCapitalR], \[ScriptCapitalQ]p[_], \[ScriptCapitalQ]m[_], \[ScriptCapitalS]p[_], \[ScriptCapitalS]m[_]}, 2];
SetOrder[{d\[ScriptX][_], d\[Theta]p[_], d\[Theta]m[_]}, 3];


Clear[expadj]
expadj[A_,B_] := Module[{comms},
	comms = NestWhileList[Expand @ Commutator[A, #] &, B, # =!=0 &];
	Expand @ Sum[comms[[i]] / (i-1)!, {i, Length@comms}]
];

Clear[getDiffOp];
getDiffOp[op_] := Module[{},
	expadj[
		- Sum[\[ScriptX][\[Mu]]\[CenterDot]\[ScriptCapitalP][\[Mu]], {\[Mu], d}]
		- Sum[\[Theta]p[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]m[\[Alpha]] + \[Theta]m[\[Alpha]]\[CenterDot]\[ScriptCapitalQ]p[\[Alpha]], {\[Alpha], 2}]
	, op] /. {
		\[ScriptCapitalP][\[Mu]_]   :> d\[ScriptX][\[Mu]],
		\[ScriptCapitalD]       :> \[CapitalDelta],
		\[ScriptCapitalK][\[Mu]_]   :> 0,
		\[ScriptCapitalQ]p[\[Alpha]_]  :> d\[Theta]m[\[Alpha]]  + 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]d\[ScriptX][\[Mu]], {\[Alpha]d, 2}, {\[Mu], d}],
		\[ScriptCapitalQ]m[\[Alpha]d_] :> d\[Theta]p[\[Alpha]d] + 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[\[Alpha]] \[CenterDot]d\[ScriptX][\[Mu]], {\[Alpha], 2},  {\[Mu], d}],
		\[ScriptCapitalS]p[\[Alpha]_]  :> 0,
		\[ScriptCapitalS]m[\[Alpha]d_] :> 0
	} // Expand
]


Table[
	getDiffOp[\[ScriptCapitalP][\[Mu]]] - (
		d\[ScriptX][\[Mu]]
), {\[Mu], d}]


getDiffOp[\[ScriptCapitalD]] - (
	+ \[CapitalDelta]
	+ Sum[\[ScriptX][\[Mu]]\[CenterDot]d\[ScriptX][\[Mu]], {\[Mu], d}]
	+ 1/2 Sum[\[Theta]p[a]\[CenterDot]d\[Theta]p[a] + \[Theta]m[a]\[CenterDot]d\[Theta]m[a], {a, 2}]
) // Expand


Table[getDiffOp[\[ScriptCapitalM][\[Mu], \[Nu]]] - (
	+ \[ScriptCapitalM][\[Mu], \[Nu]]
	- \[ScriptX][\[Mu]]\[CenterDot]d\[ScriptX][\[Nu]] + \[ScriptX][\[Nu]]\[CenterDot]d\[ScriptX][\[Mu]]
	+ Sum[mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]d\[Theta]p[\[Beta]d], {\[Alpha]d, 2}, {\[Beta]d, 2}]
	+ Sum[m [\[Mu], \[Nu]][\[Alpha],  \[Beta]]  \[Theta]m[\[Alpha]] \[CenterDot]d\[Theta]m[\[Beta]],  {\[Alpha], 2},  {\[Beta], 2}]
), {\[Mu], d}, {\[Nu], d}] // Expand // Flatten // DeleteDuplicates



getDiffOp[\[ScriptCapitalR]] - (
	+ \[ScriptCapitalR]
	+ Sum[\[Theta]m[a]\[CenterDot]d\[Theta]m[a] - \[Theta]p[a]\[CenterDot]d\[Theta]p[a], {a, 2}]
) // Expand


Table[getDiffOp[\[ScriptCapitalK][\[Mu]]] - (
	- Sum[\[ScriptX][\[Nu]]\[CenterDot]\[ScriptX][\[Nu]], {\[Nu], d}] \[CenterDot] d\[ScriptX][\[Mu]]
	+ 2 \[ScriptX][\[Mu]] \[CenterDot] Sum[\[ScriptX][\[Nu]]\[CenterDot]d\[ScriptX][\[Nu]], {\[Nu], d}]
	+ 2 \[CapitalDelta] \[ScriptX][\[Mu]]
	- 2 Sum[\[ScriptX][\[Nu]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Nu], d}]
	+ (d-1)/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]\[ScriptCapitalR], {\[Alpha], 2}, {\[Alpha]d, 2}]
	- 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] mb[\[Nu], \[Rho]][\[Alpha]d, \[Beta]d] \[Theta]p[\[Beta]d]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]\[ScriptCapitalM][\[Nu], \[Rho]]
		, {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Beta]d, 2}, {\[Nu], d}, {\[Rho], d}]
	+ 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] m[\[Nu], \[Rho]][\[Beta], \[Alpha]] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Beta]]\[CenterDot]\[ScriptCapitalM][\[Nu], \[Rho]]
		, {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Beta], 2}, {\[Nu], d}, {\[Rho], d}]
	+ \[ScriptX][\[Mu]]\[CenterDot]Sum[\[Theta]p[\[Alpha]d]\[CenterDot]d\[Theta]p[\[Alpha]d] + \[Theta]m[\[Alpha]d]\[CenterDot]d\[Theta]m[\[Alpha]d], {\[Alpha]d, 2}]
	- 2 Sum[m[\[Mu], \[Nu]][\[Alpha], \[Beta]] \[ScriptX][\[Nu]]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]d\[Theta]m[\[Beta]], {\[Alpha], 2}, {\[Beta], 2}, {\[Nu], d}]
	- 2 Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptX][\[Nu]]\[CenterDot]\[Theta]p[\[Beta]d]\[CenterDot]d\[Theta]p[\[Alpha]d], {\[Alpha]d, 2}, {\[Beta]d, 2}, {\[Nu], d}]
	+ (d-2)/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}] \[CenterDot] Sum[\[Theta]m[\[Alpha]]\[CenterDot]d\[Theta]m[\[Alpha]], {\[Alpha], 2}]
	- (d-2)/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}] \[CenterDot] Sum[\[Theta]p[\[Alpha]d]\[CenterDot]d\[Theta]p[\[Alpha]d], {\[Alpha]d, 2}]
	- (d-2)/4 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Alpha]], {\[Alpha], 2}, {\[Alpha]d, 2}] \[CenterDot] 
		  Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]d\[ScriptX][\[Mu]], {\[Alpha], 2}, {\[Alpha]d, 2}, {\[Mu], d}]
), {\[Mu], d}] // Expand // CollectCD


Table[getDiffOp[\[ScriptCapitalQ]p[\[Alpha]]] - (
	d\[Theta]m[\[Alpha]]
	- 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]p[\[Alpha]d]\[CenterDot]d\[ScriptX][\[Mu]], {\[Alpha]d, 2}, {\[Mu], d}]
), {\[Alpha], 2}] // Expand // Flatten // DeleteDuplicates
Table[getDiffOp[\[ScriptCapitalQ]m[\[Alpha]d]] - (
	d\[Theta]p[\[Alpha]d]
	- 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[\[Alpha]]\[CenterDot]d\[ScriptX][\[Mu]], {\[Alpha], 2}, {\[Mu], d}]
), {\[Alpha]d, 2}] // Expand // Flatten // DeleteDuplicates


Table[getDiffOp[\[ScriptCapitalS]p[\[Alpha]d]] - (
	- \[CapitalDelta] \[Theta]p[\[Alpha]d]
	- (d-1)/2 \[Theta]p[\[Alpha]d]\[CenterDot]\[ScriptCapitalR]
	+ Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[Theta]p[\[Beta]d]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Beta]d, 2}, {\[Mu], d}, {\[Nu], d}]
	+ Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptX][\[Mu]]\[CenterDot]d\[Theta]m[\[Alpha]], {\[Alpha], 2}, {\[Mu], d}]
	+ Sum[(
		+ (d-2)/4 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Gamma]d, \[Sigma]d] 
		+ 1/2 Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] mb[\[Mu], \[Nu]][\[Sigma]d, \[Gamma]d], {\[Mu], d}, {\[Nu], d}]
		) \[Theta]p[\[Beta]d]\[CenterDot]\[Theta]p[\[Gamma]d]\[CenterDot]d\[Theta]p[\[Sigma]d], {\[Beta]d, 2}, {\[Gamma]d, 2}, {\[Sigma]d, 2}]
	+ Sum[(
		- d/4 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Alpha], \[Beta]] 
		+ 1/2 Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] m[\[Mu], \[Nu]][\[Alpha], \[Beta]], {\[Mu], d}, {\[Nu], d}]
		) \[Theta]p[\[Beta]d]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]d\[Theta]m[\[Beta]], {\[Beta]d, 2}, {\[Alpha], 2}, {\[Beta], 2}]
	+ Sum[(
		+ (d-1)/12 \[Delta][\[Alpha]d, \[Beta]d] \[CapitalSigma][\[Rho]][\[Alpha], \[Gamma]d]
		+ 1/12 Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] (
			+ \[CapitalSigma][\[Rho]][\[Alpha], \[Sigma]d] mb[\[Mu], \[Nu]][\[Sigma]d, \[Gamma]d]
			- m[\[Mu], \[Nu]][\[Alpha], \[Sigma]d] \[CapitalSigma][\[Rho]][\[Sigma]d, \[Gamma]d]), {\[Mu], d}, {\[Nu], d}, {\[Sigma]d, 2}]
		) \[Theta]p[\[Beta]d]\[CenterDot]\[Theta]p[\[Gamma]d]\[CenterDot]\[Theta]m[\[Alpha]]\[CenterDot]d\[ScriptX][\[Rho]], {\[Rho], d}, {\[Beta]d, 2}, {\[Gamma]d, 2}, {\[Alpha], 2}]
	+ Sum[(-1/2 \[Delta][\[Mu], \[Nu]]\[Delta][\[Alpha]d, \[Beta]d] - mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d]) \[ScriptX][\[Mu]]\[CenterDot]\[Theta]p[\[Beta]d]\[CenterDot]d\[ScriptX][\[Nu]], {\[Beta]d, 2}, {\[Mu], d}, {\[Nu], d}]
), {\[Alpha]d, 2}] // CollectCD // Flatten // DeleteDuplicates


Table[getDiffOp[\[ScriptCapitalS]m[\[Alpha]]] - (
	- \[CapitalDelta] \[Theta]m[\[Alpha]]
	+ (d-1)/2 \[Theta]m[\[Alpha]]\[CenterDot]\[ScriptCapitalR]
	+ Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[Theta]m[\[Beta]]\[CenterDot]\[ScriptCapitalM][\[Mu], \[Nu]], {\[Beta], 2}, {\[Mu], d}, {\[Nu], d}]
	+ Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptX][\[Mu]]\[CenterDot]d\[Theta]p[\[Alpha]d], {\[Alpha]d, 2}, {\[Mu], d}]
	+ Sum[(
		+ (d-2)/4 \[Delta][\[Alpha], \[Beta]] \[Delta][\[Gamma], \[Sigma]] 
		+ 1/2 Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] m[\[Mu], \[Nu]][\[Gamma], \[Sigma]], {\[Mu], d}, {\[Nu], d}]
		) \[Theta]m[\[Beta]]\[CenterDot]\[Theta]m[\[Gamma]]\[CenterDot]d\[Theta]m[\[Sigma]], {\[Beta], 2}, {\[Gamma], 2}, {\[Sigma], 2}]
	+ Sum[(
		- d/4 \[Delta][\[Alpha]d, \[Beta]d] \[Delta][\[Alpha], \[Beta]] 
		+ 1/2 Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d], {\[Mu], d}, {\[Nu], d}]
		) \[Theta]m[\[Beta]]\[CenterDot]\[Theta]p[\[Alpha]d]\[CenterDot]d\[Theta]p[\[Beta]d], {\[Beta], 2}, {\[Alpha]d, 2}, {\[Beta]d, 2}]
	+ Sum[(
		+ (d-1)/12 \[Delta][\[Alpha], \[Beta]] \[CapitalSigma][\[Rho]][\[Gamma], \[Alpha]d]
		- 1/12 Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]]  (
			+ \[CapitalSigma][\[Rho]][\[Gamma], \[Sigma]d] mb[\[Mu], \[Nu]][\[Sigma]d, \[Alpha]d]
			- m[\[Mu], \[Nu]][\[Gamma], \[Sigma]d] \[CapitalSigma][\[Rho]][\[Sigma]d, \[Alpha]d]), {\[Mu], d}, {\[Nu], d}, {\[Sigma]d, 2}]
		) \[Theta]m[\[Beta]]\[CenterDot]\[Theta]m[\[Gamma]]\[CenterDot]\[Theta]p[\[Alpha]d]\[CenterDot]d\[ScriptX][\[Rho]], {\[Rho], d}, {\[Beta], 2}, {\[Gamma], 2}, {\[Alpha]d, 2}]
	+ Sum[(-1/2 \[Delta][\[Mu], \[Nu]]\[Delta][\[Alpha], \[Beta]] - m[\[Mu], \[Nu]][\[Beta], \[Alpha]]) \[ScriptX][\[Mu]]\[CenterDot]\[Theta]m[\[Beta]]\[CenterDot]d\[ScriptX][\[Nu]], {\[Beta], 2}, {\[Mu], d}, {\[Nu], d}]
), {\[Alpha], 1}] // CollectCD[#, Simplify] & // Flatten // DeleteDuplicates


Fermion[\[Theta]m[_][_], \[Theta]p[_][_]];
Boson[expr];
SetOrder[der[_, _], 5];
ders = Flatten[{
	Table[d\[ScriptX][\[Mu]], {\[Mu], d}],
	Table[d\[Theta]m[a], {a, 2}],
	Table[d\[Theta]p[a], {a, 2}]
}];
derivs = Flatten[{
	Table[GD[expr, x[i][\[Mu]]], {\[Mu], d}],
	Table[GD[expr, \[Theta]m[i][a]], {a, 2}],
	Table[GD[expr, \[Theta]p[i][a]], {a, 2}],
	expr
}];
evalCoeff = {
	\[CapitalDelta] -> \[CapitalDelta][i],
	\[ScriptCapitalR] -> r[i],
	(* HoldPattern[\[ScriptCapitalM][a_, b_]] \[RuleDelayed] m[a, b], *)
	\[ScriptX] -> x[i],
	\[Theta]m[\[Alpha]_] :> \[Theta]m[i][\[Alpha]], 
	\[Theta]p[\[Alpha]d_] :> \[Theta]p[i][\[Alpha]d]
};


Clear[coeff]
coeff[a_ + b_, op_] := coeff[a, op] + coeff[b, op]
coeff[a_?NumQ b_, op_] := a coeff[b, op]
coeff[CenterDot[a__], op_] /; FreeQ[{a}, op] := 0
HoldPattern[coeff[CenterDot[a__, op_], op_]] := CenterDot[a]
coeff[op_, op_] := 1


prepareOp[diffOp_] := Module[{coeffs, lst},
	coeffs = Append[
		coeff[diffOp, #] & /@ ders,
		diffOp /. (# -> 0 & /@ ders)
	] /. evalCoeff;
	lst = Select[Transpose[{coeffs, derivs}], #[[1]] =!= 0 &];
	Hold[Evaluate @ Total[NonCommutativeMultiply @@@ lst]] /. NonCommutativeMultiply -> CenterDot
]


prepareOp[getDiffOp[\[ScriptCapitalP][1]]]
prepareOp[getDiffOp[\[ScriptCapitalP][2]]]
prepareOp[getDiffOp[\[ScriptCapitalP][3]]]


prepareOp[getDiffOp[\[ScriptCapitalK][1]]]
prepareOp[getDiffOp[\[ScriptCapitalK][2]]]
prepareOp[getDiffOp[\[ScriptCapitalK][3]]]


prepareOp[getDiffOp[\[ScriptCapitalD]]]
prepareOp[getDiffOp[\[ScriptCapitalR]]]


prepareOp[getDiffOp[\[ScriptCapitalM][1, 2]]]
prepareOp[getDiffOp[\[ScriptCapitalM][1, 3]]]
prepareOp[getDiffOp[\[ScriptCapitalM][2, 3]]]


prepareOp[getDiffOp[\[ScriptCapitalQ]m[1]]]
prepareOp[getDiffOp[\[ScriptCapitalQ]m[2]]]
prepareOp[getDiffOp[\[ScriptCapitalQ]p[1]]]
prepareOp[getDiffOp[\[ScriptCapitalQ]p[2]]]


prepareOp[getDiffOp[\[ScriptCapitalS]m[1]]]
prepareOp[getDiffOp[\[ScriptCapitalS]m[2]]]
prepareOp[getDiffOp[\[ScriptCapitalS]p[1]]]
prepareOp[getDiffOp[\[ScriptCapitalS]p[2]]]


(* ::Text:: *)
(*Compare explicitly for a complicated case*)


lhs = getDiffOp[\[ScriptCapitalK][1]] /. {\[ScriptCapitalM][a_, b_] :> 0, \[ScriptCapitalR] -> r[i], \[CapitalDelta] -> \[CapitalDelta][i]};
rhs = (prepareOp[getDiffOp[\[ScriptCapitalK][1]]] 
	/. Times -> CenterDot /. x[i][\[Mu]_]^2 :> x[i][\[Mu]]\[CenterDot]x[i][\[Mu]]
	/. {
		GD[expr, x[i][\[Mu]_]] :> d\[ScriptX][\[Mu]],
		GD[expr, \[Theta]m[i][\[Mu]_]] :> d\[Theta]m[\[Mu]],
		GD[expr, \[Theta]p[i][\[Mu]_]] :> d\[Theta]p[\[Mu]],
		x[i] -> \[ScriptX],
		\[Theta]p[i] -> \[Theta]p,
		\[Theta]m[i] -> \[Theta]m
	} 
	/. expr -> 1 
	// ReleaseHold
);
lhs - rhs


(* ::Subsection:: *)
(*Collect differential operators 3d*)


(* ::Subsubsection::Closed:: *)
(*Generic*)


SetNumeric[\[CapitalDelta][_]];
SetNumeric[r[_]];
Fermion[\[Theta]m[_][_], \[Theta]p[_][_]];
GD[x[i_][\[Mu]_],   x[j_][\[Nu]_]]  := \[Delta][i, j] \[Delta][\[Mu], \[Nu]];
GD[x[_][_],     \[Theta]m[_][_]]   := 0;
GD[x[_][_],     \[Theta]p[_][_]]   := 0;
GD[\[Theta]m[i_][\[Alpha]_],  \[Theta]m[j_][\[Beta]_]] := \[Delta][i, j] \[Delta][\[Alpha], \[Beta]];
GD[\[Theta]m[_][_],    x[_][_]]    := 0;
GD[\[Theta]m[_][_],    \[Theta]p[_][_]]   := 0;
GD[\[Theta]p[i_][\[Alpha]d_], \[Theta]p[j_][\[Beta]d_]]:= \[Delta][i, j] \[Delta][\[Alpha]d, \[Beta]d];
GD[\[Theta]p[_][_],    x[_][_]]    := 0;
GD[\[Theta]p[_][_],    \[Theta]m[_][_]]   := 0;


twoPointOp[name_] := (
	name[i__][expr_] := Total[name[#][expr] & /@ {i}]
);
allDiffOps = Flatten @ {
	Table[{\[ScriptCapitalP]d[\[Mu]], \[ScriptCapitalK]d[\[Mu]]}, {\[Mu], d}],
	Table[\[ScriptCapitalM]d[\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}],
	{\[ScriptCapitalD]d, \[ScriptCapitalR]d},
	Table[{\[ScriptCapitalQ]md[a], \[ScriptCapitalQ]pd[a], \[ScriptCapitalS]md[a], \[ScriptCapitalS]pd[a]}, {a, 2}]
};
twoPointOp /@ allDiffOps;


(* ::Subsubsection::Closed:: *)
(*Without \[ScriptCapitalM]*)


\[ScriptCapitalP]d[1][i_][expr_] := GD[expr,x[i][1]];
\[ScriptCapitalP]d[2][i_][expr_] := GD[expr,x[i][2]];
\[ScriptCapitalP]d[3][i_][expr_] := GD[expr,x[i][3]];
\[ScriptCapitalK]d[1][i_][expr_] := ((-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2]) r[i]-\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1] r[i]+2 \[CapitalDelta][i] x[i][1])\[CenterDot]expr+(2 x[i][1] x[i][2])\[CenterDot]GD[expr,x[i][2]]+(2 x[i][1] x[i][3])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1]^2-x[i][2]^2-x[i][3]^2)\[CenterDot]GD[expr,x[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3] \[Theta]m[i][1]+x[i][1] \[Theta]m[i][2]-I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1] \[Theta]m[i][1]+I x[i][2] \[Theta]m[i][1]+x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][3] \[Theta]p[i][1]+x[i][1] \[Theta]p[i][2]+I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1] \[Theta]p[i][1]-I x[i][2] \[Theta]p[i][1]+x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalK]d[2][i_][expr_] := ((2 x[i][1] x[i][2])\[CenterDot]GD[expr,x[i][1]]+(I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2] r[i]-I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1] r[i]+2 \[CapitalDelta][i] x[i][2])\[CenterDot]expr+(2 x[i][2] x[i][3])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][1]^2+x[i][2]^2-x[i][3]^2)\[CenterDot]GD[expr,x[i][2]]+(-(1/2) I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+I x[i][3] \[Theta]m[i][1]+I x[i][1] \[Theta]m[i][2]+x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-I x[i][1] \[Theta]m[i][1]+x[i][2] \[Theta]m[i][1]+I x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-I x[i][3] \[Theta]p[i][1]-I x[i][1] \[Theta]p[i][2]+x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(1/2 I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+I x[i][1] \[Theta]p[i][1]+x[i][2] \[Theta]p[i][1]-I x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalK]d[3][i_][expr_] := ((2 x[i][1] x[i][3])\[CenterDot]GD[expr,x[i][1]]+(2 x[i][2] x[i][3])\[CenterDot]GD[expr,x[i][2]]+(-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]) r[i]+\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2] r[i]+2 \[CapitalDelta][i] x[i][3])\[CenterDot]expr+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][1]^2-x[i][2]^2+x[i][3]^2)\[CenterDot]GD[expr,x[i][3]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3] \[Theta]m[i][1]-x[i][1] \[Theta]m[i][2]-I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1] \[Theta]m[i][1]-I x[i][2] \[Theta]m[i][1]+x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][3] \[Theta]p[i][1]-x[i][1] \[Theta]p[i][2]+I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1] \[Theta]p[i][1]+I x[i][2] \[Theta]p[i][1]+x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalD]d[i_][expr_] := (\[CapitalDelta][i]\[CenterDot]expr+x[i][1]\[CenterDot]GD[expr,x[i][1]]+x[i][2]\[CenterDot]GD[expr,x[i][2]]+x[i][3]\[CenterDot]GD[expr,x[i][3]]+(1/2 \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalR]d[i_][expr_] := (r[i]\[CenterDot]expr+\[Theta]m[i][1]\[CenterDot]GD[expr,\[Theta]m[i][1]]+\[Theta]m[i][2]\[CenterDot]GD[expr,\[Theta]m[i][2]]+-\[Theta]p[i][1]\[CenterDot]GD[expr,\[Theta]p[i][1]]+-\[Theta]p[i][2]\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM]d[\[Nu], \[Mu]][i][expr];
\[ScriptCapitalM]d[\[Mu]_, \[Mu]_][i_][expr_] := 0;
\[ScriptCapitalM]d[1, 2][i_][expr_] := (-x[i][1]\[CenterDot]GD[expr,x[i][2]]+x[i][2]\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 I \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(-(1/2) I \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalM]d[1, 3][i_][expr_] := (-x[i][1]\[CenterDot]GD[expr,x[i][3]]+x[i][3]\[CenterDot]GD[expr,x[i][1]]+(1/2 \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalM]d[2, 3][i_][expr_] := (-x[i][2]\[CenterDot]GD[expr,x[i][3]]+x[i][3]\[CenterDot]GD[expr,x[i][2]]+(-(1/2) I \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalQ]md[1][i_][expr_] := (GD[expr,\[Theta]p[i][1]]+(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalQ]md[2][i_][expr_] := (GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][1]]+(1/2 I \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][2]]+(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalQ]pd[1][i_][expr_] := (GD[expr,\[Theta]m[i][1]]+(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalQ]pd[2][i_][expr_] := (GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][2]]+(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalS]md[1][i_][expr_] := ((\[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2])+x[i][1]+I x[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]+1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(r[i] \[Theta]m[i][1]-\[CapitalDelta][i] \[Theta]m[i][1])\[CenterDot]expr+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][3] \[Theta]m[i][1]+1/2 x[i][1] \[Theta]m[i][2]+1/2 I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]+(1/4 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-1/2 x[i][1] \[Theta]m[i][1]-1/2 I x[i][2] \[Theta]m[i][1]-1/2 x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(1/4 I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+1/2 I x[i][1] \[Theta]m[i][1]-1/2 x[i][2] \[Theta]m[i][1]-1/2 I x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalS]md[2][i_][expr_] := (-(\[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-(\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1])+x[i][1]-I x[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]-1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(r[i] \[Theta]m[i][2]-\[CapitalDelta][i] \[Theta]m[i][2])\[CenterDot]expr+(1/4 I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-1/2 I x[i][3] \[Theta]m[i][1]-1/2 I x[i][1] \[Theta]m[i][2]-1/2 x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+1/2 x[i][3] \[Theta]m[i][1]-1/2 x[i][1] \[Theta]m[i][2]+1/2 I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-1/2 x[i][1] \[Theta]m[i][1]+1/2 I x[i][2] \[Theta]m[i][1]-1/2 x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalS]pd[1][i_][expr_] := ((\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1]-I x[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]-1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-r[i] \[Theta]p[i][1]-\[CapitalDelta][i] \[Theta]p[i][1])\[CenterDot]expr+(-(1/4) \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][3] \[Theta]p[i][1]+1/2 x[i][1] \[Theta]p[i][2]-1/2 I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]+(1/4 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][1] \[Theta]p[i][1]+1/2 I x[i][2] \[Theta]p[i][1]-1/2 x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 I x[i][1] \[Theta]p[i][1]-1/2 x[i][2] \[Theta]p[i][1]+1/2 I x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalS]pd[2][i_][expr_] := (-(\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1]+I x[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]+1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-r[i] \[Theta]p[i][2]-\[CapitalDelta][i] \[Theta]p[i][2])\[CenterDot]expr+(-(1/4) I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+1/2 I x[i][3] \[Theta]p[i][1]+1/2 I x[i][1] \[Theta]p[i][2]-1/2 x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]+(-(1/4) \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+1/2 x[i][3] \[Theta]p[i][1]-1/2 x[i][1] \[Theta]p[i][2]-1/2 I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][1] \[Theta]p[i][1]-1/2 I x[i][2] \[Theta]p[i][1]-1/2 x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalD]md[1][i_][expr_] := (GD[expr,\[Theta]p[i][1]]-(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][3]]-(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]-(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalD]md[2][i_][expr_] := (GD[expr,\[Theta]p[i][2]]-(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][1]]-(1/2 I \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][2]]-(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalD]pd[1][i_][expr_] := (GD[expr,\[Theta]m[i][1]]-(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][3]]-(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]-(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalD]pd[2][i_][expr_] := (GD[expr,\[Theta]m[i][2]]-(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][1]]-(-(1/2) I \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][2]]-(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);


(* ::Subsubsection::Closed:: *)
(*With \[ScriptCapitalM] (whaat?)*)


\[ScriptCapitalP]d[1][i_][expr_] := GD[expr,x[i][1]];
\[ScriptCapitalP]d[2][i_][expr_] := GD[expr,x[i][2]];
\[ScriptCapitalP]d[3][i_][expr_] := GD[expr,x[i][3]];
\[ScriptCapitalK]d[1][i_][expr_] := ((-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2]) r[i]-\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1] r[i]+2 \[CapitalDelta][i] x[i][1])\[CenterDot]expr+(2 x[i][1] x[i][2])\[CenterDot]GD[expr,x[i][2]]+(2 x[i][1] x[i][3])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1]^2-x[i][2]^2-x[i][3]^2)\[CenterDot]GD[expr,x[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3] \[Theta]m[i][1]+x[i][1] \[Theta]m[i][2]-I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1] \[Theta]m[i][1]+I x[i][2] \[Theta]m[i][1]+x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][3] \[Theta]p[i][1]+x[i][1] \[Theta]p[i][2]+I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1] \[Theta]p[i][1]-I x[i][2] \[Theta]p[i][1]+x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalK]d[2][i_][expr_] := ((2 x[i][1] x[i][2])\[CenterDot]GD[expr,x[i][1]]+(I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2] r[i]-I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1] r[i]+2 \[CapitalDelta][i] x[i][2])\[CenterDot]expr+(2 x[i][2] x[i][3])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][1]^2+x[i][2]^2-x[i][3]^2)\[CenterDot]GD[expr,x[i][2]]+(-(1/2) I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+I x[i][3] \[Theta]m[i][1]+I x[i][1] \[Theta]m[i][2]+x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-I x[i][1] \[Theta]m[i][1]+x[i][2] \[Theta]m[i][1]+I x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-I x[i][3] \[Theta]p[i][1]-I x[i][1] \[Theta]p[i][2]+x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(1/2 I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+I x[i][1] \[Theta]p[i][1]+x[i][2] \[Theta]p[i][1]-I x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalK]d[3][i_][expr_] := ((2 x[i][1] x[i][3])\[CenterDot]GD[expr,x[i][1]]+(2 x[i][2] x[i][3])\[CenterDot]GD[expr,x[i][2]]+(-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]) r[i]+\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2] r[i]+2 \[CapitalDelta][i] x[i][3])\[CenterDot]expr+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-x[i][1]^2-x[i][2]^2+x[i][3]^2)\[CenterDot]GD[expr,x[i][3]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3] \[Theta]m[i][1]-x[i][1] \[Theta]m[i][2]-I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1] \[Theta]m[i][1]-I x[i][2] \[Theta]m[i][1]+x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][3] \[Theta]p[i][1]-x[i][1] \[Theta]p[i][2]+I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1] \[Theta]p[i][1]+I x[i][2] \[Theta]p[i][1]+x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalD]d[i_][expr_] := (\[CapitalDelta][i]\[CenterDot]expr+x[i][1]\[CenterDot]GD[expr,x[i][1]]+x[i][2]\[CenterDot]GD[expr,x[i][2]]+x[i][3]\[CenterDot]GD[expr,x[i][3]]+(1/2 \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalR]d[i_][expr_] := (r[i]\[CenterDot]expr+\[Theta]m[i][1]\[CenterDot]GD[expr,\[Theta]m[i][1]]+\[Theta]m[i][2]\[CenterDot]GD[expr,\[Theta]m[i][2]]+-\[Theta]p[i][1]\[CenterDot]GD[expr,\[Theta]p[i][1]]+-\[Theta]p[i][2]\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalM]d[\[Mu]_, \[Nu]_][i_][expr_] /; \[Mu]>\[Nu] := -\[ScriptCapitalM]d[\[Nu], \[Mu]][i][expr];
\[ScriptCapitalM]d[\[Mu]_, \[Mu]_][i_][expr_] := 0;
\[ScriptCapitalM]d[1, 2][i_][expr_] := (-x[i][1]\[CenterDot]GD[expr,x[i][2]]+x[i][2]\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 I \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(-(1/2) I \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]);
\[ScriptCapitalM]d[1, 3][i_][expr_] := (-x[i][1]\[CenterDot]GD[expr,x[i][3]]+x[i][3]\[CenterDot]GD[expr,x[i][1]]+(1/2 \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalM]d[2, 3][i_][expr_] := (-x[i][2]\[CenterDot]GD[expr,x[i][3]]+x[i][3]\[CenterDot]GD[expr,x[i][2]]+(-(1/2) I \[Theta]m[i][1])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(1/2 I \[Theta]p[i][1])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]);
\[ScriptCapitalQ]md[1][i_][expr_] := (GD[expr,\[Theta]p[i][1]]+(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalQ]md[2][i_][expr_] := (GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][1]]+(1/2 I \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][2]]+(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalQ]pd[1][i_][expr_] := (GD[expr,\[Theta]m[i][1]]+(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][3]]+(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalQ]pd[2][i_][expr_] := (GD[expr,\[Theta]m[i][2]]+(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][1]]+(-(1/2) I \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][2]]+(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalS]md[1][i_][expr_] := ((\[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2])+x[i][1]+I x[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]+1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(r[i] \[Theta]m[i][1]-\[CapitalDelta][i] \[Theta]m[i][1])\[CenterDot]expr+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][3] \[Theta]m[i][1]+1/2 x[i][1] \[Theta]m[i][2]+1/2 I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]+(1/4 \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-1/2 x[i][1] \[Theta]m[i][1]-1/2 I x[i][2] \[Theta]m[i][1]-1/2 x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(1/4 I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+1/2 I x[i][1] \[Theta]m[i][1]-1/2 x[i][2] \[Theta]m[i][1]-1/2 I x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalS]md[2][i_][expr_] := (-(\[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-(\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1])+x[i][1]-I x[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]-1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(r[i] \[Theta]m[i][2]-\[CapitalDelta][i] \[Theta]m[i][2])\[CenterDot]expr+(1/4 I \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-1/2 I x[i][3] \[Theta]m[i][1]-1/2 I x[i][1] \[Theta]m[i][2]-1/2 x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+1/2 x[i][3] \[Theta]m[i][1]-1/2 x[i][1] \[Theta]m[i][2]+1/2 I x[i][2] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]-1/2 x[i][1] \[Theta]m[i][1]+1/2 I x[i][2] \[Theta]m[i][1]-1/2 x[i][3] \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalS]pd[1][i_][expr_] := ((\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][2]]+(\[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]+x[i][1]-I x[i][2])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(1/2 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]-1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]+x[i][3])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-r[i] \[Theta]p[i][1]-\[CapitalDelta][i] \[Theta]p[i][1])\[CenterDot]expr+(-(1/4) \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][3] \[Theta]p[i][1]+1/2 x[i][1] \[Theta]p[i][2]-1/2 I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]+(1/4 \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][1] \[Theta]p[i][1]+1/2 I x[i][2] \[Theta]p[i][1]-1/2 x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) I \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 I x[i][1] \[Theta]p[i][1]-1/2 x[i][2] \[Theta]p[i][1]+1/2 I x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalS]pd[2][i_][expr_] := (-(\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2])\[CenterDot]GD[expr,\[Theta]p[i][1]]+(\[Theta]m[i][1]\[CenterDot]\[Theta]p[i][2]+x[i][1]+I x[i][2])\[CenterDot]GD[expr,\[Theta]m[i][1]]+(-(1/2) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]+1/2 \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][2]-x[i][3])\[CenterDot]GD[expr,\[Theta]m[i][2]]+(-r[i] \[Theta]p[i][2]-\[CapitalDelta][i] \[Theta]p[i][2])\[CenterDot]expr+(-(1/4) I \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+1/2 I x[i][3] \[Theta]p[i][1]+1/2 I x[i][1] \[Theta]p[i][2]-1/2 x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]+(-(1/4) \[Theta]m[i][2]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]+1/2 x[i][3] \[Theta]p[i][1]-1/2 x[i][1] \[Theta]p[i][2]-1/2 I x[i][2] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]+(-(1/4) \[Theta]m[i][1]\[CenterDot]\[Theta]p[i][1]\[CenterDot]\[Theta]p[i][2]-1/2 x[i][1] \[Theta]p[i][1]-1/2 I x[i][2] \[Theta]p[i][1]-1/2 x[i][3] \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalD]md[1][i_][expr_] := (GD[expr,\[Theta]p[i][1]]-(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][3]]-(-(1/2) \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][1]]-(-(1/2) I \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalD]md[2][i_][expr_] := (GD[expr,\[Theta]p[i][2]]-(-(1/2) \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][1]]-(1/2 I \[Theta]m[i][1])\[CenterDot]GD[expr,x[i][2]]-(1/2 \[Theta]m[i][2])\[CenterDot]GD[expr,x[i][3]]);
\[ScriptCapitalD]pd[1][i_][expr_] := (GD[expr,\[Theta]m[i][1]]-(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][3]]-(-(1/2) \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][1]]-(1/2 I \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][2]]);
\[ScriptCapitalD]pd[2][i_][expr_] := (GD[expr,\[Theta]m[i][2]]-(-(1/2) \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][1]]-(-(1/2) I \[Theta]p[i][1])\[CenterDot]GD[expr,x[i][2]]-(1/2 \[Theta]p[i][2])\[CenterDot]GD[expr,x[i][3]]);


(* ::Subsection::Closed:: *)
(*Check commutation relations*)


Boson[f];
addDiff = {
	\[ScriptCapitalD] -> \[ScriptCapitalD]d[1],
	\[ScriptCapitalR] -> \[ScriptCapitalR]d[1],
	\[ScriptCapitalP][\[Mu]_] :> \[ScriptCapitalP]d[\[Mu]][1],
	\[ScriptCapitalK][\[Mu]_] :> \[ScriptCapitalK]d[\[Mu]][1],
	\[ScriptCapitalM][\[Mu]_, \[Nu]_] :> \[ScriptCapitalM]d[\[Mu], \[Nu]][1],
	\[ScriptCapitalQ]p[\[Alpha]_] :> \[ScriptCapitalQ]pd[\[Alpha]][1],
	\[ScriptCapitalQ]m[\[Alpha]_] :> \[ScriptCapitalQ]md[\[Alpha]][1],
	\[ScriptCapitalS]p[\[Alpha]_] :> \[ScriptCapitalS]pd[\[Alpha]][1],
	\[ScriptCapitalS]m[\[Alpha]_] :> \[ScriptCapitalS]md[\[Alpha]][1],
	\[ScriptCapitalD]m[\[Alpha]_] :> \[ScriptCapitalD]md[\[Alpha]][1],
	\[ScriptCapitalD]p[\[Alpha]_] :> \[ScriptCapitalD]pd[\[Alpha]][1]
};
checkComm[op1_, op2_, res_] := (
	+ (op1[op2[f]] /. addDiff)
	- (op2[op1[f]] /. addDiff)
	+ (res /. addDiff /. {a_[1] :> a[1][f]})
) // GExpand;
checkAntiComm[op1_, op2_, res_] := (
	+ (op1[op2[f]] /. addDiff)
	+ (op2[op1[f]] /. addDiff)
	+ (res /. addDiff /. {a_[1] :> a[1][f]})
) // GExpand;

Join[
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]], \[ScriptCapitalP][\[Mu]]], {\[Mu], d}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalP][\[Mu]],  \[ScriptCapitalP][\[Mu]]], {\[Mu], d}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalK][\[Mu]], -\[ScriptCapitalK][\[Mu]]], {\[Mu], d}],
	Table[checkComm[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalP][\[Nu]], 2(\[Delta][\[Mu],\[Nu]] \[ScriptCapitalD] - \[ScriptCapitalM][\[Mu], \[Nu]])], {\[Mu], d}, {\[Nu], d}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalM][\[Rho], \[Sigma]], -(
		+ \[Delta][\[Mu], \[Rho]] \[ScriptCapitalM][\[Nu], \[Sigma]]
		- \[Delta][\[Nu], \[Rho]] \[ScriptCapitalM][\[Mu], \[Sigma]]
		- \[Delta][\[Mu], \[Sigma]] \[ScriptCapitalM][\[Nu], \[Rho]]
		+ \[Delta][\[Nu], \[Sigma]] \[ScriptCapitalM][\[Mu], \[Rho]]
	)], {\[Mu], d}, {\[Nu], d}, {\[Rho], d}, {\[Sigma], d}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalP][\[Rho]], - (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalP][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalP][\[Mu]])]
	, {\[Mu], d}, {\[Nu], d}, {\[Rho], d}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalK][\[Rho]], - (\[Delta][\[Mu], \[Rho]] \[ScriptCapitalK][\[Nu]] - \[Delta][\[Nu], \[Rho]] \[ScriptCapitalK][\[Mu]])]
	, {\[Mu], d}, {\[Nu], d}, {\[Rho], d}],
	Table[checkAntiComm[\[ScriptCapitalQ]p[\[Alpha]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[\[CapitalSigma][\[Mu]][\[Alpha],\[Alpha]d] \[ScriptCapitalP][\[Mu]], {\[Mu], d}]], {\[Alpha], 2}, {\[Alpha]d, 2}],
	Table[checkAntiComm[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalS]m[\[Alpha]], Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalK][\[Mu]], {\[Mu], d}]], {\[Alpha], 2}, {\[Alpha]d, 2}],
	Table[checkAntiComm[\[ScriptCapitalS]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 
		+ \[Delta][\[Alpha], \[Beta]] (\[ScriptCapitalD] - (d-1)/2 \[ScriptCapitalR]) 
		- Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}]]
	, {\[Alpha], 2}, {\[Beta], 2}],
	Table[checkAntiComm[\[ScriptCapitalS]p[\[Alpha]d], \[ScriptCapitalQ]m[\[Beta]d], 
		+ \[Delta][\[Alpha]d, \[Beta]d] (\[ScriptCapitalD] + (d-1)/2 \[ScriptCapitalR]) 
		- Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalM][\[Mu], \[Nu]], {\[Mu], d}, {\[Nu], d}]]
	, {\[Alpha]d, 2}, {\[Beta]d, 2}],
	Table[checkComm[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]p[\[Alpha]],  + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]p[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], d}, {\[Alpha],  2}],
	Table[checkComm[\[ScriptCapitalK][\[Mu]], \[ScriptCapitalQ]m[\[Alpha]d], + Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[ScriptCapitalS]m[\[Alpha]] , {\[Alpha],  2}]], {\[Mu], d}, {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]p[\[Alpha]d], - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]p[\[Alpha]],  {\[Alpha],  2}]], {\[Mu], d}, {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalP][\[Mu]], \[ScriptCapitalS]m[\[Alpha]],  - Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Alpha]] \[ScriptCapitalQ]m[\[Alpha]d], {\[Alpha]d, 2}]], {\[Mu], d}, {\[Alpha] , 2}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]p[\[Alpha]], Sum[m[\[Mu], \[Nu]][\[Alpha], \[Beta]] \[ScriptCapitalQ]p[\[Beta]], {\[Beta], 2}]]
	, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalQ]m[\[Alpha]d], Sum[mb[\[Mu], \[Nu]][\[Beta]d, \[Alpha]d] \[ScriptCapitalQ]m[\[Beta]d], {\[Beta]d, 2}]]
	, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]p[\[Alpha]d], -Sum[mb[\[Mu], \[Nu]][\[Alpha]d, \[Beta]d] \[ScriptCapitalS]p[\[Beta]d], {\[Beta]d, 2}]]
	, {\[Mu], d}, {\[Nu], d}, {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalM][\[Mu], \[Nu]], \[ScriptCapitalS]m[\[Alpha]], -Sum[m[\[Mu], \[Nu]][\[Beta], \[Alpha]] \[ScriptCapitalS]m[\[Beta]], {\[Beta], 2}]]
	, {\[Mu], d}, {\[Nu], d}, {\[Alpha], 2}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalQ]p[\[Alpha]],  +1/2 \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalQ]m[\[Alpha]d], +1/2 \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalS]p[\[Alpha]d], -1/2 \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalD], \[ScriptCapitalS]m[\[Alpha]],  -1/2 \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}],
	Table[checkComm[\[ScriptCapitalR], \[ScriptCapitalQ]p[\[Alpha]],  + \[ScriptCapitalQ]p[\[Alpha]]],  {\[Alpha], 2}],
	Table[checkComm[\[ScriptCapitalR], \[ScriptCapitalQ]m[\[Alpha]d], - \[ScriptCapitalQ]m[\[Alpha]d]], {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalR], \[ScriptCapitalS]p[\[Alpha]d], + \[ScriptCapitalS]p[\[Alpha]d]], {\[Alpha]d, 2}],
	Table[checkComm[\[ScriptCapitalR], \[ScriptCapitalS]m[\[Alpha]],  - \[ScriptCapitalS]m[\[Alpha]]],  {\[Alpha], 2}],
	Table[checkAntiComm[\[ScriptCapitalD]m[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 0], {\[Alpha], 2}, {\[Beta], 2}],
	Table[checkAntiComm[\[ScriptCapitalD]m[\[Alpha]], \[ScriptCapitalQ]m[\[Beta]], 0], {\[Alpha], 2}, {\[Beta], 2}],
	Table[checkAntiComm[\[ScriptCapitalD]p[\[Alpha]], \[ScriptCapitalQ]p[\[Beta]], 0], {\[Alpha], 2}, {\[Beta], 2}],
	Table[checkAntiComm[\[ScriptCapitalD]p[\[Alpha]], \[ScriptCapitalQ]m[\[Beta]], 0], {\[Alpha], 2}, {\[Beta], 2}]
] // Flatten // DeleteDuplicates


(* ::Subsection::Closed:: *)
(*Inversion*)


joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m|th12|th13|\[Xi]]&) :> a\[CenterDot]b}
);


\[Theta]4[i_] := \[Theta]p[i][1] \[CenterDot] \[Theta]p[i][2] \[CenterDot] \[Theta]m[i][1] \[CenterDot] \[Theta]m[i][2];
deninv[i_] := powerExpr[Sum[x[i][\[Nu]]^2, {\[Nu], d}] + 1/2 \[Theta]4[i], -1, (\[Theta]p|\[Theta]m)];
xinv[i_][\[Mu]_] := x[i][\[Mu]] deninv[i];
\[Theta]pinv[i_][\[Alpha]d_] := (
	- 1/2 \[Theta]p[i][\[Alpha]d] \[CenterDot] Sum[\[Theta]p[i][\[Beta]]\[CenterDot]\[Theta]m[i][\[Beta]], {\[Beta], 2}]
	+ Sum[\[CapitalSigma]b[\[Mu]][\[Alpha]d, \[Beta]d] x[i][\[Mu]] \[Theta]p[i][\[Beta]d], {\[Mu], 3}, {\[Beta]d, 2}]) \[CenterDot] deninv[i];
\[Theta]minv[i_][\[Alpha]_] := (
	- 1/2 \[Theta]m[i][\[Alpha]] \[CenterDot] Sum[\[Theta]p[i][\[Beta]]\[CenterDot]\[Theta]m[i][\[Beta]], {\[Beta], 2}]
	- Sum[\[CapitalSigma]b[\[Mu]][\[Beta], \[Alpha]] x[i][\[Mu]] \[Theta]m[i][\[Beta]], {\[Mu], 3}, {\[Beta], 2}]) \[CenterDot] deninv[i];


invert = {x -> xinv, \[Theta]p -> \[Theta]pinv, \[Theta]m -> \[Theta]minv};
invShiftInv[expr_, shift_] := Module[{expr2, num, den, inum, iden},
	expr2 = expr /. invert /. shift // GExpand // Together;
	{num, den} = {Numerator@expr2, Denominator@expr2};
	{inum, iden} = {num, den} /. invert  // GExpand // joinCD // CollectCD[#, Factor] &;
	inum \[CenterDot] powerExpr[iden, -1, \[Theta]p|\[Theta]m|\[Xi]] // GExpand // CollectCD[#, Factor] &
];
invShiftInvSer[expr_, shift_, var_] := Normal[
	Series[invShiftInv[expr, shift], {var, 0, 1}]
] // Coefficient[#, var] &;
invSq[expr_] := invShiftInv[expr, {}]


(* ::Text:: *)
(*Check that it squares to one*)


Table[invSq[x[1][\[Mu]]], {\[Mu], 3}]
Table[invSq[\[Theta]p[1][\[Alpha]]], {\[Alpha], 2}]
Table[invSq[\[Theta]m[1][\[Alpha]]], {\[Alpha], 2}]


(* ::Text:: *)
(*Check it acts like the differential operator K*)


basis = Flatten @ {
	Table[x[1][\[Mu]], {\[Mu], d}],
	Table[{\[Theta]p[1][\[Alpha]], \[Theta]m[1][\[Alpha]]}, {\[Alpha], 2}]
};


ruleDiffOp = Table[{x[1][\[Nu]] -> x[1][\[Nu]] + a, \[ScriptCapitalK]d[\[Nu]][1]}, {\[Nu], 3}];
Table[
	lhs = invShiftInvSer[term, rdo[[1]], a];
	rhs = rdo[[2]][term] /. (\[CapitalDelta]|r)[_] :> 0 // GExpand;
	lhs + rhs
, {term, basis}, {rdo, ruleDiffOp}] // CollectCD


(* ::Text:: *)
(*Check it acts as differential operator Sp/\[ScriptCapitalS]m*)


Fermion[\[Xi]];
ruleDiffOp = Table[{{
		\[Theta]m[1][\[Alpha]] -> \[Theta]m[1][\[Alpha]] + a \[Xi],
		x[1][\[Mu]_] -> x[1][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] a \[Xi] \[CenterDot] \[Theta]p[1][\[Alpha]d], {\[Alpha]d, 2}]
	}, 
	\[ScriptCapitalS]pd[\[Alpha]][1]
}, {\[Alpha], 2}];
Table[
	lhs = invShiftInvSer[term, rdo[[1]], a];
	rhs = \[Xi] \[CenterDot] rdo[[2]][term] /. (\[CapitalDelta]|r)[_] :> 0 // GExpand;
	lhs + rhs
, {term, basis}, {rdo, ruleDiffOp}] // CollectCD


Fermion[\[Xi]];
ruleDiffOp = Table[{{
		\[Theta]p[1][\[Alpha]d] -> \[Theta]p[1][\[Alpha]d] + a \[Xi],
		x[1][\[Mu]_] -> x[1][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] a \[Xi] \[CenterDot] \[Theta]m[1][\[Alpha]], {\[Alpha], 2}]
	}, 
	\[ScriptCapitalS]md[\[Alpha]d][1]
}, {\[Alpha]d, 2}];
Table[
	lhs = invShiftInvSer[term, rdo[[1]], a];
	rhs = \[Xi] \[CenterDot] rdo[[2]][term] /. (\[CapitalDelta]|r)[_] :> 0 // GExpand;
	lhs - rhs
, {term, basis}, {rdo, ruleDiffOp}] // CollectCD


(* ::Subsection:: *)
(*Blocks  \[LeftAngleBracket] \[Phi] Oh Oh \[RightAngleBracket] 3d boundary*)


(* ::Subsubsection::Closed:: *)
(*Bosonic blocks*)


\[ScriptCapitalC]2defect[i__][expr_] := (
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 Sum[\[ScriptCapitalP]d[\[Mu]][i][\[ScriptCapitalK]d[\[Mu]][i][expr]] + \[ScriptCapitalK]d[\[Mu]][i][\[ScriptCapitalP]d[\[Mu]][i][expr]], {\[Mu], 2}]
	- \[ScriptCapitalM]d[1, 2][i][\[ScriptCapitalM]d[1, 2][i][expr]]
)


Clear[pref];
SetNumeric[j, w[_]];
\[Chi]v = (x[1][1]^2 + x[1][2]^2) / x[1][3]^2;
restore\[Chi] = Solve[\[Chi]v == \[Chi], x[1][3]] // First;
pref = (
	(x[1][1] w[1] + x[1][2] w[2])^j 
	(x[1][1]^2 + x[1][2]^2)^(-j/2) 
	(x[1][3]^2)^(-1/2(\[CapitalDelta][1] + \[CapitalDelta][2] - \[CapitalDelta][3]))
);
GD[f_[\[Chi]], a_] := D[f[\[Chi]], \[Chi]] GD[\[Chi]v, a];
diffEq = (\[ScriptCapitalC]2defect[1][pref f[\[Chi]]] - c2 pref f[\[Chi]]) / pref /. (\[Theta]p|\[Theta]m)[_][_] :> 0 // ExpandAll;
diffEq = % /. restore\[Chi] /. \[CapitalDelta][2] -> \[CapitalDelta]23 + \[CapitalDelta][3] /. w[1] -> I w[2] // Simplify


bosBlock[\[CapitalDelta]_, \[CapitalDelta]23_, j_][\[Chi]_] := (
	\[Chi]^( -1/2 (\[CapitalDelta] + \[CapitalDelta]23)) 
	Hypergeometric2F1[1/2(\[CapitalDelta] + \[CapitalDelta]23 - j), 1/2(\[CapitalDelta] + \[CapitalDelta]23 + j), \[CapitalDelta], -1/\[Chi]]
);
diffEq /. f -> bosBlock[\[CapitalDelta], \[CapitalDelta]23, j] /. c2 -> \[CapitalDelta](\[CapitalDelta]- 2) // Series[#, {\[Chi], Infinity, 10}] &


(* ::Subsubsection::Closed:: *)
(*Susy blocks*)


joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m]&) :> a\[CenterDot]b}
);


comm [i___][A_, B_][expr_] := A[i][B[i][expr]] - B[i][A[i][expr]];
acomm[i___][A_, B_][expr_] := A[i][B[i][expr]] + B[i][A[i][expr]];
\[ScriptCapitalQ]pard[1][i___][expr_] := \[ScriptCapitalQ]pd[1][i][expr] + \[ScriptCapitalQ]md[2][i][expr];
\[ScriptCapitalQ]pard[2][i___][expr_] := \[ScriptCapitalQ]pd[2][i][expr] + \[ScriptCapitalQ]md[1][i][expr];
\[ScriptCapitalS]pard[1][i___][expr_] := \[ScriptCapitalS]pd[2][i][expr] + \[ScriptCapitalS]md[1][i][expr];
\[ScriptCapitalS]pard[2][i___][expr_] := \[ScriptCapitalS]pd[1][i][expr] + \[ScriptCapitalS]md[2][i][expr];
\[ScriptCapitalC]2defect[i__][expr_] := (
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 Sum[acomm[i][\[ScriptCapitalP]d[a], \[ScriptCapitalK]d[a]][expr], {a, 2}]
	- \[ScriptCapitalM]d[1, 2][i][\[ScriptCapitalM]d[1, 2][i][expr]]
	+ 1/4 Sum[comm[i][\[ScriptCapitalS]pard[a], \[ScriptCapitalQ]pard[a]][expr], {a, 2}]
);


(* ::Text:: *)
(*Check the Casimir indeed commutes (takes a bit long)*)


(* {
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalP]d[a]][f], {a, 2}],
	comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalD]d][f],
	comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalM]d[1, 2]][f],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalK]d[a]][f], {a, 2}],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalQ]pard[a]][f], {a, 2}],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalS]pard[a]][f], {a, 2}]
} // GExpand // Flatten *)


Clear[y];
yV[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
restoreY = First @ Solve[{
	yV[1][1] == y[1][1],
	yV[1][2] == y[1][2],
	yV[1][3] == y[1][3]
}, {x[1][1], x[1][2], x[1][3]}];
Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][yV[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}]
] // Flatten // DeleteDuplicates


Clear[pref];
pref = (
	(y[1][1] + I y[1][2])^j
	(y[1][1]^2 + y[1][2]^2)^(-j/2)
	y[1][3]^(-(\[CapitalDelta][1]+\[CapitalDelta][2]-\[CapitalDelta][3]))
);
funs = f[1][\[Chi]] + inv f[2][\[Chi]];
invV = \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2] \[CenterDot] powerExpr[yV[1][3], -1, (\[Theta]p|\[Theta]m)] // GExpand // CollectCD;
\[Chi]v = Sum[y[1][a]^2, {a, 2}] / y[1][3]^2;
restore\[Chi] = Solve[\[Chi]v == \[Chi], y[1][1]] // First;
GD[y[i_][\[Mu]_], a_] := GD[yV[i][\[Mu]], a]
GD[inv, a_] := GD[invV, a]
GD[f_[\[Chi]], a_] := D[f[\[Chi]], \[Chi]] GD[\[Chi]v, a];


eqs = (\[ScriptCapitalC]2defect[1][pref funs] - c2 pref funs) / pref // GExpand // CollectCD;


eqs = x[1][3] / y[1][3] eqs /. r[1] -> \[CapitalDelta][1] // CollectCD[#, Factor] &;
eqs = eqs /. restoreY // GExpand // joinCD // CollectCD[#, Factor] &;
eqs = % /. \[Theta]p[1][1]\[CenterDot]\[Theta]p[1][2] -> inv y[1][3] /. restore\[Chi] // 
	CollectCD[#, Collect[#, inv, Collect[#, f_[\[Chi]], Factor] &] &] &;
neqs = % /. inv^2 :> 0 /. (\[Theta]p|\[Theta]m)[_][_] :> 0 // CoefficientList[#, inv] &
sol = Solve[neqs == 0, {f[1]''[\[Chi]], f[2]''[\[Chi]]}] // First
eqs /. sol // CollectCD[#, Together] & // (# /. inv -> invV // joinCD) & 


(* ::Text:: *)
(*Write for Latex*)


neqs2 = neqs /. {\[CapitalDelta][2] -> Subscript[\[CapitalDelta], 23] + \[CapitalDelta][3], \[CapitalDelta][1] -> Subscript[\[CapitalDelta], 1], f[i_]/;i==1||i==2 :> Subscript[f, i]} // Collect[#, f_[\[Chi]], FullSimplify] &
neqs2[[2]] + neqs2[[1]] // Collect[#, f_[\[Chi]], FullSimplify] &


bosBlock[\[CapitalDelta]_, \[CapitalDelta]23_, j_][\[Chi]_] := (
	\[Chi]^(-1/2(\[CapitalDelta]+\[CapitalDelta]23)) 
	Hypergeometric2F1[1/2(\[CapitalDelta]+\[CapitalDelta]23-j), 1/2(\[CapitalDelta]+\[CapitalDelta]23+j), \[CapitalDelta], -1/\[Chi]]
);
neqs /. {
	f[1] -> (
		+ a[1] bosBlock[\[CapitalDelta],   \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
		+ a[2] bosBlock[\[CapitalDelta]+1, \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
	&),
	f[2] -> (
		+ a[3] bosBlock[\[CapitalDelta],   \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
		+ a[4] bosBlock[\[CapitalDelta]+1, \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
	&),
	c2 -> \[CapitalDelta](\[CapitalDelta]-1)
} //. {
	a[3] -> -a[1] (\[CapitalDelta]-\[CapitalDelta][1]),
	a[4] -> a[2] (-1+\[CapitalDelta]+\[CapitalDelta][1])
} // Series[#, {\[Chi], \[Infinity], 10}] &


(* ::Subsection::Closed:: *)
(*Blocks  \[LeftAngleBracket] \[Phi] Oh Oh \[RightAngleBracket] 3d line*)


(* ::Subsubsection::Closed:: *)
(*Bosonic blocks*)


\[ScriptCapitalC]2defect[i__][expr_] := (
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 \[ScriptCapitalP]d[3][i][\[ScriptCapitalK]d[3][i][expr]] + \[ScriptCapitalK]d[3][i][\[ScriptCapitalP]d[3][i][expr]]
	- \[ScriptCapitalM]d[1, 2][i][\[ScriptCapitalM]d[1, 2][i][expr]]
)


Clear[pref];
SetNumeric[j, w[_]];
\[Chi]v = (x[1][1]^2 + x[1][2]^2) / x[1][3]^2;
restore\[Chi] = Solve[\[Chi]v == \[Chi], x[1][3]] // First;
pref = (
	(x[1][1] w[1] + x[1][2] w[2])^j 
	(x[1][1]^2 + x[1][2]^2)^(-j/2) 
	(x[1][3]^2)^(-1/2(\[CapitalDelta][1] + \[CapitalDelta][2] - \[CapitalDelta][3]))
);
GD[f_[\[Chi]], a_] := D[f[\[Chi]], \[Chi]] GD[\[Chi]v, a];
diffEq = (\[ScriptCapitalC]2defect[1][pref f[\[Chi]]] - c2 pref f[\[Chi]]) / pref /. (\[Theta]p|\[Theta]m)[_][_] :> 0 // ExpandAll;
diffEq = % /. restore\[Chi] /. \[CapitalDelta][2] -> \[CapitalDelta]23 + \[CapitalDelta][3] /. w[1] -> I w[2] // Simplify


bosBlock[\[CapitalDelta]_, \[CapitalDelta]23_, j_][\[Chi]_] := (
	\[Chi]^( -1/2 (\[CapitalDelta] + \[CapitalDelta]23)) 
	Hypergeometric2F1[1/2(\[CapitalDelta] + \[CapitalDelta]23 - j), 1/2(\[CapitalDelta] + \[CapitalDelta]23 + j), \[CapitalDelta], -1/\[Chi]]
);
diffEq /. f -> bosBlock[\[CapitalDelta], \[CapitalDelta]23, j] /. c2 -> \[CapitalDelta](\[CapitalDelta]- 2) // Series[#, {\[Chi], Infinity, 10}] &


(* ::Subsubsection::Closed:: *)
(*Susy blocks*)


inv = \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2];
\[ScriptCapitalM]d[1, 2][1][inv] + a I \[ScriptCapitalR]d[1][inv] /. r[_] :> 0 // GExpand


joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m]&) :> a\[CenterDot]b}
);


comm [i___][A_, B_][expr_] := A[i][B[i][expr]] - B[i][A[i][expr]];
acomm[i___][A_, B_][expr_] := A[i][B[i][expr]] + B[i][A[i][expr]];
\[ScriptCapitalQ]pard[1][i___][expr_] := \[ScriptCapitalQ]pd[1][i][expr] + \[ScriptCapitalQ]md[2][i][expr];
\[ScriptCapitalQ]pard[2][i___][expr_] := \[ScriptCapitalQ]pd[2][i][expr] + \[ScriptCapitalQ]md[1][i][expr];
\[ScriptCapitalS]pard[1][i___][expr_] := \[ScriptCapitalS]pd[2][i][expr] + \[ScriptCapitalS]md[1][i][expr];
\[ScriptCapitalS]pard[2][i___][expr_] := \[ScriptCapitalS]pd[1][i][expr] + \[ScriptCapitalS]md[2][i][expr];
\[ScriptCapitalC]2defect[i__][expr_] := (
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 Sum[acomm[i][\[ScriptCapitalP]d[a], \[ScriptCapitalK]d[a]][expr], {a, 2}]
	- \[ScriptCapitalM]d[1, 2][i][\[ScriptCapitalM]d[1, 2][i][expr]]
	+ 1/4 Sum[comm[i][\[ScriptCapitalS]pard[a], \[ScriptCapitalQ]pard[a]][expr], {a, 2}]
);


(* ::Text:: *)
(*Check the Casimir indeed commutes (takes a bit long)*)


(* {
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalP]d[a]][f], {a, 2}],
	comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalD]d][f],
	comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalM]d[1, 2]][f],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalK]d[a]][f], {a, 2}],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalQ]pard[a]][f], {a, 2}],
	Table[comm[1][\[ScriptCapitalC]2defect, \[ScriptCapitalS]pard[a]][f], {a, 2}]
} // GExpand // Flatten *)


Clear[y];
yV[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
restoreY = First @ Solve[{
	yV[1][1] == y[1][1],
	yV[1][2] == y[1][2],
	yV[1][3] == y[1][3]
}, {x[1][1], x[1][2], x[1][3]}];
Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][yV[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}]
] // Flatten // DeleteDuplicates


Clear[pref];
pref = (
	(y[1][1] + I y[1][2])^j
	(y[1][1]^2 + y[1][2]^2)^(-j/2)
	y[1][3]^(-(\[CapitalDelta][1]+\[CapitalDelta][2]-\[CapitalDelta][3]))
);
funs = f[1][\[Chi]] + inv f[2][\[Chi]];
invV = \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2] \[CenterDot] powerExpr[yV[1][3], -1, (\[Theta]p|\[Theta]m)] // GExpand // CollectCD;
\[Chi]v = Sum[y[1][a]^2, {a, 2}] / y[1][3]^2;
restore\[Chi] = Solve[\[Chi]v == \[Chi], y[1][1]] // First;
GD[y[i_][\[Mu]_], a_] := GD[yV[i][\[Mu]], a]
GD[inv, a_] := GD[invV, a]
GD[f_[\[Chi]], a_] := D[f[\[Chi]], \[Chi]] GD[\[Chi]v, a];


eqs = (\[ScriptCapitalC]2defect[1][pref funs] - c2 pref funs) / pref // GExpand // CollectCD;


eqs = x[1][3] / y[1][3] eqs /. r[1] -> \[CapitalDelta][1] // CollectCD[#, Factor] &;
eqs = eqs /. restoreY // GExpand // joinCD // CollectCD[#, Factor] &;
eqs = % /. \[Theta]p[1][1]\[CenterDot]\[Theta]p[1][2] -> inv y[1][3] /. restore\[Chi] // 
	CollectCD[#, Collect[#, inv, Collect[#, f_[\[Chi]], Factor] &] &] &;
neqs = % /. inv^2 :> 0 /. (\[Theta]p|\[Theta]m)[_][_] :> 0 // CoefficientList[#, inv] &
sol = Solve[neqs == 0, {f[1]''[\[Chi]], f[2]''[\[Chi]]}] // First
eqs /. sol // CollectCD[#, Together] & // (# /. inv -> invV // joinCD) & 


(* ::Text:: *)
(*Write for Latex*)


neqs2 = neqs /. {\[CapitalDelta][2] -> Subscript[\[CapitalDelta], 23] + \[CapitalDelta][3], \[CapitalDelta][1] -> Subscript[\[CapitalDelta], 1], f[i_]/;i==1||i==2 :> Subscript[f, i]} // Collect[#, f_[\[Chi]], FullSimplify] &
neqs2[[2]] + neqs2[[1]] // Collect[#, f_[\[Chi]], FullSimplify] &


bosBlock[\[CapitalDelta]_, \[CapitalDelta]23_, j_][\[Chi]_] := (
	\[Chi]^(-1/2(\[CapitalDelta]+\[CapitalDelta]23)) 
	Hypergeometric2F1[1/2(\[CapitalDelta]+\[CapitalDelta]23-j), 1/2(\[CapitalDelta]+\[CapitalDelta]23+j), \[CapitalDelta], -1/\[Chi]]
);
neqs /. {
	f[1] -> (
		+ a[1] bosBlock[\[CapitalDelta],   \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
		+ a[2] bosBlock[\[CapitalDelta]+1, \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
	&),
	f[2] -> (
		+ a[3] bosBlock[\[CapitalDelta],   \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
		+ a[4] bosBlock[\[CapitalDelta]+1, \[CapitalDelta][2]-\[CapitalDelta][3], j][#]
	&),
	c2 -> \[CapitalDelta](\[CapitalDelta]-1)
} //. {
	a[3] -> -a[1] (\[CapitalDelta]-\[CapitalDelta][1]),
	a[4] -> a[2] (-1+\[CapitalDelta]+\[CapitalDelta][1])
} // Series[#, {\[Chi], \[Infinity], 10}] &


(* ::Subsection::Closed:: *)
(*Line, two pt fun defect blocks*)


(* ::Subsubsection::Closed:: *)
(*Define distances*)


(* ::Text:: *)
(*Invariant respect covariant derivatives*)


SetNumeric[a];
Clear[y, yt];
y[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
yt[i_][\[Mu]_] := x[i][\[Mu]] + 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];


(* ::Text:: *)
(*Invariant respect \[ScriptCapitalQ] and \[ScriptCapitalP]*)


z1  = y[1][1]  -   \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1];
z2  = y[1][2]  + I \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1];
zt1 = yt[2][1] +   \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2];
zt2 = yt[2][2] + I \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2];
z3  = y[1][3] - yt[2][3] - \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][1];
GD[zz1,  a_] := GD[z1,  a]
GD[zz2,  a_] := GD[z2,  a]
GD[zz3,  a_] := GD[z3,  a]
GD[zzt1, a_] := GD[zt1, a]
GD[zzt2, a_] := GD[zt2, a]
restoreZ = Solve[{
	z1 == zz1,
	z2 == zz2,
	zt1 == zzt1,
	zt2 == zzt2,
	z3 == zz3
}, {x[1][1], x[1][2], x[2][1], x[2][2], x[1][3]}] // First;


(* ::Text:: *)
(*Checks*)


Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][y[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][yt[2][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][\[Theta]m[2][\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}]
] // Flatten // DeleteDuplicates

invs = {\[Theta]p[1][2], \[Theta]m[2][2], z1, z2, zt1, zt2, z3};
{
	\[ScriptCapitalQ]pd[1][1, 2][invs],
	\[ScriptCapitalQ]md[1][1, 2][invs],
	\[ScriptCapitalP]d[3][1, 2][invs] 
} // Expand // Flatten // DeleteDuplicates

transRot[i__][expr_] := \[ScriptCapitalR]d[i][expr] - I \[ScriptCapitalM]d[1, 2][i][expr];
{
	transRot[1, 2][z1\[CenterDot]z1 + z2\[CenterDot]z2],
	transRot[1, 2][zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2],
	transRot[1, 2][z1\[CenterDot]zt1 + z2\[CenterDot]zt2],
	transRot[1, 2][z3],
	transRot[1, 2][\[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]]
} /. r[_] :> 0 // GExpand // DeleteDuplicates


(* ::Subsubsection::Closed:: *)
(*Find invariants*)


\[Eta]v = (zz1 zzt1 + zz2 zzt2) / (Sqrt[zz1^2 + zz2^2] Sqrt[zzt1^2 + zzt2^2]);
\[Phi]v = Sqrt[zz1^2 + zz2^2] / Sqrt[zzt1^2 + zzt2^2];
\[Xi]v = (
	zz3^2 / (Sqrt[zz1^2 + zz2^2] Sqrt[zzt1^2 + zzt2^2])
	- 2 \[Eta]v + \[Phi]v + 1 / \[Phi]v
);
\[Theta]v = \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2] (zz1^2 + zz2^2)^(-1/4) (zzt1^2 + zzt2^2)^(-1/4);


GD[f_[\[Eta], \[Xi], \[Phi]], a_] := (
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Eta]] GD[\[Eta]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Xi]] GD[\[Xi]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Phi]] GD[\[Phi]v, a]
);
joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m]&) :> a\[CenterDot]b}
);


expr = {
	\[ScriptCapitalK]d[3][1, 2][\[Eta]v + \[Theta]v g[\[Eta], \[Xi], \[Phi]]],
	\[ScriptCapitalK]d[3][1, 2][\[Xi]v + \[Theta]v g[\[Eta], \[Xi], \[Phi]]]
} /. {\[CapitalDelta][_]|r[_] -> 0} // GExpand // joinCD // CollectCD[#, Simplify] &;
expr /. restoreZ // GExpand // joinCD // CollectCD[#, Simplify] &


Solve[((zz3 (zz2 zzt1-zz1 zzt2))/(zzt1-I zzt2)
+(-I zz1+zz2) (zz1^2+zz2^2)^(1/4) (zzt1^2+zzt2^2)^(1/4) g[\[Eta],\[Xi],\[Phi]])==0, g[\[Eta],\[Xi],\[Phi]]] // FullSimplify
Solve[((zz3 (zz1^2+zz2^2+zz3^2+2 I zz2 zzt1+zzt1^2-2 I zz1 zzt2+zzt2^2))/(zzt1-I zzt2)
-(zz1+I zz2) (zz1^2+zz2^2)^(1/4) (zzt1^2+zzt2^2)^(1/4) g[\[Eta],\[Xi],\[Phi]])==0, g[\[Eta],\[Xi],\[Phi]]] // FullSimplify


(* ::Text:: *)
(*Final sanity check*)


randR = # -> RandomReal[] & /@ {zz1, zz2, zz3, zzt1, zzt2};
invs = {
	\[Eta]v + \[Theta]v (I zz3 (-zz2 zzt1+zz1 zzt2))/((zz1+I zz2) (zz1^2+zz2^2)^(1/4) (zzt1-I zzt2) (zzt1^2+zzt2^2)^(1/4)),
	\[Xi]v + \[Theta]v (zz3 (zz1^2+zz2^2+zz3^2+2 I zz2 zzt1+zzt1^2-2 I zz1 zzt2+zzt2^2))/((zz1+I zz2) (zz1^2+zz2^2)^(1/4) (zzt1-I zzt2) (zzt1^2+zzt2^2)^(1/4))
};
expr = Table[{
	\[ScriptCapitalD]d[1, 2][inv],
	\[ScriptCapitalP]d[3][1, 2][inv],
	\[ScriptCapitalQ]pd[1][1, 2][inv],
	\[ScriptCapitalQ]md[1][1, 2][inv],
	transRot[1, 2][inv],
	\[ScriptCapitalD]pd[1][1][inv],
	\[ScriptCapitalD]pd[2][1][inv],
	\[ScriptCapitalD]md[1][2][inv],
	\[ScriptCapitalD]md[2][2][inv],
	\[ScriptCapitalK]d[3][1, 2][inv]
}, {inv, invs}] /. {\[CapitalDelta][_]|r[_] -> 0} /. restoreZ /. randR // GExpand // joinCD // Chop


(* ::Subsubsection::Closed:: *)
(*Find prefactor*)


(* ::Text:: *)
(*Find the prefactor*)


SetNumeric[\[CapitalDelta]p];
pref=(zz1^2+zz2^2)^(-(\[CapitalDelta]p/2)) (zzt1^2+zzt2^2)^(-(\[CapitalDelta]p/2));
expr = (
	\[ScriptCapitalK]d[3][1, 2][pref (1 + \[Theta]v g[\[Eta], \[Xi], \[Phi]])] / pref
	/. {\[CapitalDelta][_]|r[1] -> \[CapitalDelta]p, r[2] -> -\[CapitalDelta]p} /. restoreZ
	// GExpand // joinCD // Together // CollectCD[#, Simplify] &
) // CollectCD


Solve[((zz3 \[CapitalDelta]p)/(zzt1-I zzt2)
-((zz1+I zz2) g[\[Eta],\[Xi],\[Phi]])/((zz1^2+zz2^2)^(1/4) (zzt1^2+zzt2^2)^(1/4)))==0,g[\[Eta],\[Xi],\[Phi]]] // Simplify


(* ::Text:: *)
(*Sanity check with all generators*)


inv = pref (
	+ 1 
	+ \[Theta]v ((zz1^2+zz2^2)^(1/4) zz3 (zzt1^2+zzt2^2)^(1/4) \[CapitalDelta]p)/((zz1+I zz2) (zzt1-I zzt2))
);
{
	\[ScriptCapitalD]d[1, 2][inv] / pref,
	\[ScriptCapitalP]d[3][1, 2][inv] / pref,
	\[ScriptCapitalQ]pd[1][1, 2][inv] / pref,
	\[ScriptCapitalQ]md[1][1, 2][inv] / pref,
	transRot[1, 2][inv] / pref,
	\[ScriptCapitalD]pd[1][1][inv] / pref,
	\[ScriptCapitalD]pd[2][1][inv] / pref,
	\[ScriptCapitalD]md[1][2][inv] / pref,
	\[ScriptCapitalD]md[2][2][inv] / pref,
	\[ScriptCapitalK]d[3][1, 2][inv] / pref
} /. {\[CapitalDelta][_]|r[1] -> \[CapitalDelta]p, r[2] -> -\[CapitalDelta]p} /. restoreZ // GExpand // joinCD // Together // CollectCD[#, Simplify] &


(* ::Subsubsection::Closed:: *)
(*Apply Casimir*)


(* ::Text:: *)
(*Defect Casimir*)


\[ScriptCapitalC]2defect[i__][expr_] := (
	\[ScriptCapitalD]d[i][\[ScriptCapitalD]d[i][expr]]
	- 1/2 (\[ScriptCapitalP]d[3][i][\[ScriptCapitalK]d[3][i][expr]] + \[ScriptCapitalK]d[3][i][\[ScriptCapitalP]d[3][i][expr]])
	- transRot[i][transRot[i][expr]]
	+ 1/2 (\[ScriptCapitalS]pd[1][i][\[ScriptCapitalQ]md[1][i][expr]] - \[ScriptCapitalQ]md[1][i][\[ScriptCapitalS]pd[1][i][expr]])
	+ 1/2 (\[ScriptCapitalS]md[1][i][\[ScriptCapitalQ]pd[1][i][expr]] - \[ScriptCapitalQ]pd[1][i][\[ScriptCapitalS]md[1][i][expr]])
)


(* ::Text:: *)
(*Check that it commutes as expected*)


ops = {\[ScriptCapitalD]d, \[ScriptCapitalP]d[3], \[ScriptCapitalK]d[3], transRot, \[ScriptCapitalQ]pd[1], \[ScriptCapitalQ]md[1], \[ScriptCapitalS]pd[1], \[ScriptCapitalS]md[1]};
Table[
	\[ScriptCapitalC]2defect[1][op[1][f]] - op[1][\[ScriptCapitalC]2defect[1][f]]
, {op, ops}] // GExpand


GD[f_[\[Eta], \[Chi]], a_] := (
	+ D[f[\[Eta], \[Chi]], \[Eta]] GD[invs[[1]], a]
	+ D[f[\[Eta], \[Chi]], \[Chi]] GD[invs[[2]] + 2 invs[[1]], a]
);


casEq = \[ScriptCapitalC]2defect[1][f] /. {\[CapitalDelta][_]|r[1] -> \[CapitalDelta]p, r[2] -> -\[CapitalDelta]p} // GExpand;
xs = {x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]};
cr = CoefficientRules[casEq, xs];
keys = joinCD[GExpand[Times@@(xs^#) /. restoreZ]] & /@ Keys[cr];
casEq = Total[MapThread[GExpand[#1 \[CenterDot] #2] &, {keys, Values[cr]}]];


casEq = GExpand[casEq \[CenterDot] powerExpr[inv, -1, \[Theta]p|\[Theta]m]] /. f -> inv g[\[Eta], \[Chi]] // GExpand;
casEq = Collect[casEq, f_[\[Eta], \[Chi]], CollectCD[#, Simplify] &]


sqrt1\[Eta]2 = (
	powerExpr[1-invs[[1]]\[CenterDot]invs[[1]], 1/2, \[Theta]p|\[Theta]m] 
	// GExpand // Collect[#, f_[\[Eta], \[Xi]], CollectCD[#, Simplify] &] & 
	// # //. Sqrt[a_ b_] :> Sqrt[a] Sqrt[b] //. Sqrt[1/a_] :> 1/Sqrt[a] //. Sqrt[a_^2] :> a &
);


casEqAns = (
	+ (1-\[Eta]\[Eta]^2) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- \[Eta]\[Eta] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- I (1-2\[CapitalDelta]p) sqrt1\[Eta]2 \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	- (-1+\[CapitalDelta]p) \[CapitalDelta]p g[\[Eta], \[Chi]]
	+ (\[Chi]\[Chi]^2-4) \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
	+ 2 \[Chi]\[Chi] \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta], \[Chi]]
);
casEqAns = casEqAns /. {\[Eta]\[Eta] -> invs[[1]], \[Chi]\[Chi] -> invs[[2]] + 2 invs[[1]]} // GExpand // joinCD;
casEq - casEqAns // Collect[#, f_[\[Eta], \[Chi]], CollectCD[#, Simplify] &] &


(* ::Subsection:: *)
(*\[LeftAngleBracket] \[Phi] Oh \[RightAngleBracket] 3d boundary*)


(* ::Subsubsection:: *)
(*Susy blocks*)


joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m]&) :> a\[CenterDot]b}
);


\[ScriptCapitalQ]pard[1][i___][expr_] := \[ScriptCapitalQ]pd[1][i][expr] + \[ScriptCapitalQ]md[2][i][expr];
\[ScriptCapitalQ]pard[2][i___][expr_] := \[ScriptCapitalQ]pd[2][i][expr] + \[ScriptCapitalQ]md[1][i][expr];
\[ScriptCapitalS]pard[1][i___][expr_] := \[ScriptCapitalS]pd[2][i][expr] + \[ScriptCapitalS]md[1][i][expr];
\[ScriptCapitalS]pard[2][i___][expr_] := \[ScriptCapitalS]pd[1][i][expr] + \[ScriptCapitalS]md[2][i][expr];


Clear[y];
yV[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
restoreY = First @ Solve[{
	yV[1][1] == y[1][1],
	yV[1][2] == y[1][2],
	yV[1][3] == y[1][3]
}, {x[1][1], x[1][2], x[1][3]}];
GD[y[i_][\[Mu]_], a_] := GD[yV[i][\[Mu]], a]
Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][yV[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}]
] // Flatten // DeleteDuplicates


Clear[pref];
pref = (
	(y[1][1]^2 + y[1][2]^2 + y[1][3]^2)^(-\[CapitalDelta][2])
	y[1][3]^(-\[CapitalDelta][1]+\[CapitalDelta][2])
) (1 + (\[CapitalDelta][1] - \[CapitalDelta][2]) \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2] / y[1][3]);
invV = (y[1][1]^2 + y[1][2]^2 + y[1][3]^2) / y[1][3]^2;
GD[f_[inv], a_] := D[f[inv], inv] GD[invV, a]


{
	\[ScriptCapitalD]d[1, 2][pref],
	\[ScriptCapitalM]d[1, 2][1, 2][pref],
	Table[\[ScriptCapitalK]d[a][1][pref], {a, 2}],
	Table[\[ScriptCapitalS]pard[a][1][pref], {a, 2}]
} /. restoreY /. r[1] -> \[CapitalDelta][1] // GExpand // joinCD // Flatten // Simplify


eom = (
	+ \[ScriptCapitalD]md[1][1][\[ScriptCapitalD]md[2][1][pref]] 
	- \[ScriptCapitalD]md[2][1][\[ScriptCapitalD]md[1][1][pref]] 
) /. {\[CapitalDelta][1] -> 1/2, \[CapitalDelta][2] -> 1/2} // GExpand // joinCD // CollectCD[#, Factor] &


Solve[(-1+4 b-2 \[CapitalDelta][1]-2 \[CapitalDelta][2])==0,b]


SetNumeric[a, b, c];
Clear[pref];
ratioV = (y[1][1]^2 + y[1][2]^2) / y[1][3]^2;
restoreRatio = Solve[ratioV == ratio, y[1][3]] // First;
GD[f_[ratio], a_] := D[f[ratio], ratio] GD[ratioV, a]
pref = (
	(y[1][1]^2 + y[1][2]^2 + y[1][3]^2)^(-b)
	( \[Theta]p[1][1] f[ratio] + \[Theta]p[1][2] g[ratio])
);
{
	\[ScriptCapitalD]d[1, 2][pref],
	Table[\[ScriptCapitalD]pd[a][1][pref], {a, 2}],
	(* \[ScriptCapitalM]d[1, 2][1, 2][pref], *)
	\[ScriptCapitalR]d[1, 2][pref],
	Table[\[ScriptCapitalK]d[a][1][pref], {a, 2}],
	\[ScriptCapitalS]md[1][1][pref],
	\[ScriptCapitalS]pd[2][1][pref]
} /. restoreY /. restoreRatio /. r[1] -> \[CapitalDelta][1] //. {
b->1/4 (1+2 \[CapitalDelta][1]+2 \[CapitalDelta][2]),
r[2]->1-\[CapitalDelta][1]
} // GExpand // joinCD // Flatten // Simplify // Collect[#, (\[Theta]p|\[Theta]m)[_][_], Simplify] &


DSolve[(f[ratio] (\[CapitalDelta][1]-\[CapitalDelta][2])-2 (1+ratio) Derivative[1][f][ratio])==0,f,ratio]


Clear[pref];
pref = (y[1][1]^2 + y[1][2]^2 + y[1][3]^2)^(-\[CapitalDelta][1]);
{
	\[ScriptCapitalD]d[1, 2][pref],
	\[ScriptCapitalM]d[1, 2][1, 2][pref],
	\[ScriptCapitalR]d[1, 2][pref],
	Table[\[ScriptCapitalK]d[a][1][pref], {a, 2}],
	\[ScriptCapitalS]md[1][1][pref],
	\[ScriptCapitalS]pd[2][1][pref]
} /. restoreY /. r[1] -> \[CapitalDelta][1] /. r[2] :> - \[CapitalDelta][1] /. \[CapitalDelta][2] -> \[CapitalDelta][1] // 
	GExpand // joinCD // Flatten // Simplify


eom = (
	+ \[ScriptCapitalD]md[1][1][\[ScriptCapitalD]md[2][1][pref]] 
	- \[ScriptCapitalD]md[2][1][\[ScriptCapitalD]md[1][1][pref]] 
) /. {\[CapitalDelta][1] -> \[CapitalDelta]1, \[CapitalDelta][2] -> \[CapitalDelta]2} // GExpand // joinCD // CollectCD[#, Factor] &
