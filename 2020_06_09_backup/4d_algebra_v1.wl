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


(* ::Section:: *)
(*Conventions*)


(* ::Text:: *)
(*Spacetime dimension*)


d = 3;


(* ::Subsection::Closed:: *)
(*Gamma matrices*)


Clear[\[Delta], \[CapitalSigma], \[CapitalSigma]b, m, mb]
\[Delta] = KroneckerDelta;
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
	Table[Commutator[\[ScriptCapitalJ][m], \[ScriptCapitalG]b[r]] + \[ScriptCapitalG]b[m+r], {m, 0, 0}, {r, -1/2, 1/2}]
}] // Expand // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Casimir operator*)


\[ScriptCapitalC]2def = ( 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 AntiCommutator[\[ScriptCapitalK][3], \[ScriptCapitalP][3]]
	- (-I \[ScriptCapitalM][1, 2] + \[ScriptCapitalR])\[CenterDot](-I \[ScriptCapitalM][1, 2] + \[ScriptCapitalR])
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
);
Table[Commutator[\[ScriptCapitalC]2def, op], {op, allDefOps}] // Expand // DeleteDuplicates // CollectCD


(* ::Text:: *)
(*Casimir eigenvalue*)


Expand[ 
	+ \[ScriptCapitalD]\[CenterDot]\[ScriptCapitalD]
	- 1/2 Commutator[\[ScriptCapitalK][3], \[ScriptCapitalP][3]]
	- (-I \[ScriptCapitalM][1, 2] + \[ScriptCapitalR])\[CenterDot](-I \[ScriptCapitalM][1, 2] + \[ScriptCapitalR])
	+ 1/2 AntiCommutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 AntiCommutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
] /. {
	\[ScriptCapitalD] -> \[CapitalDelta],
	\[ScriptCapitalM][1, 2] -> I(l-\[ScriptCapitalR])
} // Expand


(* ::Text:: *)
(*Contribution in the defect channel*)


(
	+ 1/2 Commutator[\[ScriptCapitalS]p[1], \[ScriptCapitalQ]m[1]]
	+ 1/2 Commutator[\[ScriptCapitalS]m[1], \[ScriptCapitalQ]p[1]]
) - (
	- \[ScriptCapitalQ]m[1]\[CenterDot]\[ScriptCapitalS]p[1]
	+ \[ScriptCapitalS]m[1]\[CenterDot]\[ScriptCapitalQ]p[1]
) // Expand


(* ::Subsection::Closed:: *)
(*d=4: OSP(1|4) subalgebra*)


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
(*d=3: Lined defect channel*)


Quit


block1[\[CapitalDelta]_][\[Chi]_] := \[Chi]^(-\[CapitalDelta]) Hypergeometric2F1[\[CapitalDelta]/2, (\[CapitalDelta]+1)/2, \[CapitalDelta]+1-1/2, 4/\[Chi]^2]
block2[s_][\[Eta]_] := Hypergeometric2F1[-s/2, (2+s-2)/2, (2-1)/2, 1-\[Eta]^2]


bosEq1 = (\[Chi]^2-4) f''[\[Chi]] + (1+1) \[Chi] f'[\[Chi]] - \[CapitalDelta](\[CapitalDelta]-1) f[\[Chi]];
bosEq2 = (\[Eta]^2-1) f''[\[Eta]] + (2-1) \[Eta] f'[\[Eta]] - s(s+2-2) f[\[Eta]];


bosEq1 /. f -> block1[\[CapitalDelta]] // Series[#, {\[Chi], Infinity, 4}] &
bosEq2 /. f -> block2[s] // Series[#, {\[Eta], 0, 4}, Assumptions-> 0<\[Eta] && \[Eta]<1] &


bosEq2
diffEq /. q -> 2
block2[s][\[Eta]]
S2block[s, 2][\[Eta]]


diffEq = (
	+ (\[Chi]^2-4) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"2", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi], \[Eta]] + (1+1) \[Chi] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi], \[Eta]]
	- ((\[Eta]^2-1) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "2"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi], \[Eta]] + (2-1) \[Eta] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi], \[Eta]])
	+ (2\[CapitalDelta]p - 1) Sqrt[1-\[Eta]^2] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Chi], \[Eta]]
	- cas f[\[Chi], \[Eta]]
);
ansatz = {
	f -> (
		+ aa[1] block1[\[CapitalDelta]][#1]     block2[s][#2]
		+ aa[2] block1[\[CapitalDelta]+1/2][#1] block2[s-1/2][#2]
		+ aa[3] block1[\[CapitalDelta]+1/2][#1] block2[s+1/2][#2]
		+ aa[4] block1[\[CapitalDelta]+1][#1]   block2[s][#2]
	& )
};


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
	HoldPattern[\[ScriptCapitalM][_, _]] -> 0,
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


(* ::Subsection::Closed:: *)
(*Collect differential operators 3d*)


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
(*Invariant intervals Boundary*)


(* ::Text:: *)
(*Invariant respect covariant derivatives*)


SetNumeric[a];
Clear[y, yt];
y[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
yt[i_][\[Mu]_] := x[i][\[Mu]] + 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][y[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][yt[2][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][\[Theta]m[2][\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}]
] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Find invariant respect \[ScriptCapitalQ] and \[ScriptCapitalP]*)


SetNumeric[kk[_]];
ansatz = (
	+ kk[1]  yy[1][1]
	+ kk[2]  yy[1][2]
	+ kk[3]  yy[1][3]
	+ kk[4]  yyt[2][1] 
	+ kk[5]  yyt[2][2]
	+ kk[6]  yyt[2][3]
	+ kk[7]  \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2]
	+ kk[8]  \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][1]
	+ kk[9]  \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2]
	+ kk[10] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1]
	+ kk[11] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	+ kk[12] \[Theta]m[2][1] \[CenterDot] \[Theta]m[2][2]
);
sol = {
	kk[4] -> I kk[5]+kk[10],
	kk[6] -> -kk[11] -kk[12],
	kk[3] -> -kk[7] -kk[8],
	kk[1] -> I kk[2] - kk[10],
	kk[8] -> -kk[11],
	kk[10] -> -2I kk[5] + kk[9],
	kk[2] -> -kk[5]
};
{
	\[ScriptCapitalQ]pd[1][1, 2][ansatz] + \[ScriptCapitalQ]md[2][1, 2][ansatz],
	\[ScriptCapitalQ]pd[2][1, 2][ansatz] + \[ScriptCapitalQ]md[1][1, 2][ansatz],
	\[ScriptCapitalP]d[1][1, 2][ansatz],
	\[ScriptCapitalP]d[2][1, 2][ansatz]
} /. {yy -> y, yyt -> yt} //. sol // Collect[#, \[Theta]m[_][_]|\[Theta]p[_][_], Factor] &
ansatz //. sol // Collect[#, kk[_], Simplify] &


(* ::Text:: *)
(*Check them:*)


invs = {
	\[Theta]p[1][1] - \[Theta]m[2][2],
	\[Theta]p[1][2] - \[Theta]m[2][1],
	y[1][1] - yt[2][1] +   \[Theta]m[2][1]\[CenterDot]\[Theta]p[1][2] +   \[Theta]m[2][2]\[CenterDot]\[Theta]p[1][1],
	y[1][2] - yt[2][2] - I \[Theta]m[2][1]\[CenterDot]\[Theta]p[1][2] + I \[Theta]m[2][2]\[CenterDot]\[Theta]p[1][1],
	y[1][3]  - \[Theta]p[1][1]\[CenterDot]\[Theta]p[1][2],
	yt[2][3] - \[Theta]m[2][1]\[CenterDot]\[Theta]m[2][2]
};
{
	\[ScriptCapitalQ]pd[1][1, 2][invs] + \[ScriptCapitalQ]md[2][1, 2][invs],
	\[ScriptCapitalQ]pd[2][1, 2][invs] + \[ScriptCapitalQ]md[1][1, 2][invs],
	\[ScriptCapitalP]d[1][1, 2][invs],
	\[ScriptCapitalP]d[2][1, 2][invs]
} // Expand // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Require invariance under \[ScriptCapitalM]*)


z1  = y[1][1] - yt[2][1] +   \[Theta]m[2][1]\[CenterDot]\[Theta]p[1][2] +   \[Theta]m[2][2]\[CenterDot]\[Theta]p[1][1];
z2  = y[1][2] - yt[2][2] - I \[Theta]m[2][1]\[CenterDot]\[Theta]p[1][2] + I \[Theta]m[2][2]\[CenterDot]\[Theta]p[1][1];
z3  = y[1][3]  - \[Theta]p[1][1]\[CenterDot]\[Theta]p[1][2];
zt3 = yt[2][3] - \[Theta]m[2][1]\[CenterDot]\[Theta]m[2][2];
th1 = \[Theta]p[1][1] - \[Theta]m[2][2];
th2 = \[Theta]p[1][2] - \[Theta]m[2][1];
{
	\[ScriptCapitalM]d[1, 2][1, 2][z1\[CenterDot]z1 + z2\[CenterDot]z2],
	\[ScriptCapitalM]d[1, 2][1, 2][z3],
	\[ScriptCapitalM]d[1, 2][1, 2][zt3],
	\[ScriptCapitalM]d[1, 2][1, 2][th1\[CenterDot]th2]
} // GExpand


\[Xi]v = (
	(z1\[CenterDot]z1 + z2\[CenterDot]z2 + (z3-zt3)\[CenterDot](z3-zt3))
	\[CenterDot] powerExpr[z3,  -1, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt3, -1, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;
\[Phi]v = zt3 \[CenterDot] powerExpr[z3, -1, \[Theta]p|\[Theta]m] // GExpand // CollectCD[#, Factor] &;


th12v = th1 \[CenterDot] th2 \[CenterDot] powerExpr[z3, -1, \[Theta]p|\[Theta]m] // GExpand // CollectCD[#, Factor] &;


\[Xi]v /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // FullSimplify
\[Phi]v /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // FullSimplify


GExpand[th1 \[CenterDot] th2]





joinCD[expr_] := (
	expr //. {a_CenterDot^b_ :> 0}
		 //. {a_Plus?(Not@FreeQ[#,CenterDot]&) b_ :> GExpand[a\[CenterDot]b]}
		 //. {a_CenterDot b_?(Not@FreeQ[#, \[Theta]p|\[Theta]m]&) :> a\[CenterDot]b}
);
restoreXParRule = Solve[{z1 == zz1, z2 == zz2}, {x[1][1], x[1][2]}] // First;
restoreThRule = {\[Theta]m[2][1] \[CenterDot] \[Theta]m[2][2] -> 
	+ \[Theta]m[2][1] \[CenterDot] \[Theta]p[1][1]
	- \[Theta]m[2][2] \[CenterDot] \[Theta]p[1][2]
	+ \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2]
	- (\[Phi] \[Xi] - (1-\[Phi])^2)^(-1/2) Sqrt[zz1^2 + zz2^2] \[CapitalTheta]
};
x23v = (
	+ z3 \[Phi] 
	+ \[Theta]m[2][1] \[CenterDot] \[Theta]m[2][2] 
	- 1/2 Sum[\[CapitalSigma][3][\[Alpha], \[Alpha]d] \[Theta]m[2][\[Alpha]]\[CenterDot]\[Theta]p[2][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}]
) // GExpand // CollectCD[#, Simplify] &;
x13v = (
	+ (\[Phi] \[Xi] - (1-\[Phi])^2)^(-1/2) Sqrt[zz1^2 + zz2^2] 
	+ 1/2 Sum[\[CapitalSigma][3][\[Alpha], \[Alpha]d] \[Theta]m[1][\[Alpha]]\[CenterDot]\[Theta]p[1][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}]
	+ \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2] 
) // GExpand // CollectCD[#, Simplify] &;
Clear[powx13, powx23];
powx13[a_] := powx13[a] = powerExpr[x13v, a, \[Theta]p|\[Theta]m];
powx23[a_] := powx23[a] = powerExpr[x23v, a, \[Theta]p|\[Theta]m];
restoreXPar[expr_] := expr /. restoreXParRule;
restoreTh[expr_] := expr /. restoreThRule;
restoreX13[expr_] := expr /. {
	x[1][3]^a_ :> powx13[a],
	x[1][3] :> x13v
};
restoreX23[expr_] := expr /. {
	x[2][3]^a_ :> powx23[a],
	x[2][3] :> x23v
};


expr = \[Xi]v // restoreXPar // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX23 // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX13 // GExpand // joinCD // CollectCD[#, Factor] &


expr = \[Phi]v // restoreXPar // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX23 // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX13 // GExpand // joinCD // CollectCD[#, Factor] &


expr = th12v // restoreXPar // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX23 // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreX13 // GExpand // joinCD // CollectCD[#, Factor] &;
expr = expr // restoreTh // GExpand // joinCD // CollectCD[#, Factor] &


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];
invAns = (
	+ \[Xi]v
	+ th12v g[\[Xi], \[Phi]]
	(* - 2 th12v \[CenterDot] (-1+\[Phi]v) \[CenterDot] powerExpr[\[Phi]v, -1, \[Theta]p|\[Theta]m] *)
) // GExpand // CollectCD;
GD[f_[\[Xi], \[Phi]], a_] := (
	+ D[f[\[Xi], \[Phi]], \[Xi]] GD[\[Xi]v, a]
	+ D[f[\[Xi], \[Phi]], \[Phi]] GD[\[Phi]v, a]
);


{
	\[ScriptCapitalD]d[1, 2][invAns],
	\[ScriptCapitalP]d[1][1, 2][invAns],
	\[ScriptCapitalP]d[2][1, 2][invAns],
	\[ScriptCapitalQ]pd[1][1, 2][invAns] + \[ScriptCapitalQ]md[2][1, 2][invAns],
	\[ScriptCapitalQ]pd[2][1, 2][invAns] + \[ScriptCapitalQ]md[1][1, 2][invAns],
	\[ScriptCapitalM]d[1, 2][1, 2][invAns],
	\[ScriptCapitalD]pd[1][1][invAns],
	\[ScriptCapitalD]pd[2][1][invAns],
	\[ScriptCapitalD]md[1][2][invAns],
	\[ScriptCapitalD]md[2][2][invAns]
} /. {\[CapitalDelta][_]|r[_] -> 0} /. randR // GExpand // Chop


expr = {
	\[ScriptCapitalK]d[1][1, 2][invAns],
	\[ScriptCapitalK]d[2][1, 2][invAns]
} /. {\[CapitalDelta][_]|r[_] -> 0} // GExpand;


expr /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0}


expr2 = expr // restoreXPar // GExpand // joinCD // CollectCD[#, Factor] &;


expr2 = expr2 // restoreX23 // GExpand // joinCD // CollectCD[#, Factor] &;


expr2 = expr2 // restoreX13 // GExpand // joinCD // CollectCD[#, Simplify] &;


expr2 = expr2 // restoreTh // GExpand // joinCD // CollectCD[#, Collect[#, \[CapitalTheta], Simplify] &] &


Solve[(-(2/\[Phi])+2 \[Phi]+g[\[Xi],\[Phi]]+\[Phi] g[\[Xi],\[Phi]]) == 0, g[\[Xi], \[Phi]]]


c1 = Coefficient[expr, g[\[Eta],\[Xi],\[Phi]]];
c2 = Coefficient[expr, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]];
c3 = expr /. {g[\[Eta],\[Xi],\[Phi]] -> 0, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 0};


Sort


c1 // CollectCD[#, Simplify] &
Cases[%, HoldPattern[CenterDot[__]], Infinity] // SortBy[#, Length] &
-\[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
\[Theta]v // CollectCD[#, Simplify] &


{c1, c2, c3} /. (\[Theta]m|\[Theta]p)[_][_] :> 0


c1 \[CenterDot] c1 // GExpand
% \[CenterDot] c1 // GExpand



 


Cases[expr, f_[\[Eta],\[Xi],\[Phi]], Infinity] // DeleteDuplicates // Sort
Cases[expr2, f_[\[Eta],\[Xi],\[Phi]], Infinity] // DeleteDuplicates // Sort


expr // GExpand


expr2 = (expr /. randR) // GExpand // CollectCD[#, Factor] & // Chop


expr /. {
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] :> 0,
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 0,
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 1,
	\[Theta]m[1][_] -> 0,
	\[Theta]p[2][_] -> 0,
	\[Theta]p[1][1] -> 0,
	\[Theta]m[2][1] -> 0
} // GExpand // CollectCD[#, Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &] & // FullSimplify
Solve[% == 0, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]] // ExpandAll // FullSimplify


{\[Eta]v, \[Xi]v, \[Phi]v, \[Theta]v, \[Eta]v\[CenterDot]\[Eta]v\[CenterDot]\[Xi]v\[CenterDot]\[Theta]v};
 expr  /. {
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] :> 0,
	(* (f^(0,1,0))[\[Eta],\[Xi],\[Phi]] \[Rule] 0,
	(f^(1,0,0))[\[Eta],\[Xi],\[Phi]] \[Rule] 1, *)
	\[Theta]m[1][_] -> 0,
	\[Theta]p[2][_] -> 0,
	\[Theta]p[1][1] -> 0,
	\[Theta]m[2][1] -> 0,
	x[2][2] -> 0,
	x[2][1] -> 1,
	x[2][3] -> 0
	(* x[1][2] \[Rule] 0 *) 
} // GExpand // CollectCD[#, Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &] & // FullSimplify
eqs = % //. {
	x[1][1]->\[Eta] \[Phi],
	x[1][2]->-Sqrt[1-\[Eta]^2] \[Phi],
	x[1][3]->-Sqrt[-1+(2 \[Eta]+\[Xi]-\[Phi]) \[Phi]],
	\[Theta]m[2][2]\[CenterDot]\[Theta]p[1][2] -> - \[Theta] Sqrt[\[Phi]]
} // FullSimplify[#, \[Phi] > 0] &


part1 = ExpandAll[eqs] /. Complex[0,_] :> 0
part2 = I (eqs - part1) // ExpandAll // Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &


Sqrt[\[Phi]] part1 // FullSimplify[#, \[Phi]>0] &


-((I Sqrt[1-\[Eta]^2] \[Theta] \[Xi] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])/Sqrt[\[Phi]])//FullForm


Solve[{x[1][1]^2+x[1][2]^2 == \[Phi]^2,
	x[1][1] == \[Eta] \[Phi]}, {x[1][1], x[1][2]}] // FullSimplify[#, \[Phi] > 0] &


Solve[((-0.7542488804229955`- 0.6844321255037191` I) g[\[Eta],\[Xi],\[Phi]]+(0.5615845786213401` +0.5059996357207578` I) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+(0.013202407892695826` -0.016405453808335926` I) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])==0, g[\[Eta],\[Xi],\[Phi]]] // Expand


inv1 = (
	(z1\[CenterDot]zt1 + z2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[1] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2] \[CenterDot] z3
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[2] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[3] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;


\[ScriptCapitalK]d[3][1, 2][inv1] /. {\[CapitalDelta][_] -> 0, r[_] -> 0} /. randR // GExpand // CollectCD // Chop


%/.a->-0.0319750237819319`+ 0.17593357165724927` I // CollectCD // Chop


Solve[((-0.0008673567763213819`- 0.0018491848350067341` I)+(0.009307262479505255` -0.006621571451512355` I) a)==0, a]


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];


(* ::Subsubsection::Closed:: *)
(*Understand bosonic*)


\[Eta]v = (
	(z1\[CenterDot]zt1 + z2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify
\[Phi]v = (
	(zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify
\[Xi]v = (
	z3\[CenterDot]z3
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify


restore = Solve[{\[Eta]v == \[Eta], \[Phi]v == \[Phi], \[Xi]v == \[Xi], x[2][1] == 1, x[2][2] == 1, x[2][3] == 0}, {x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]}] // First // Simplify


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];
bosAns = (
	+ f[\[Eta], \[Xi], \[Phi]]
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]]
	(*+ \[Eta]v
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]]*)
);
GD[f_[\[Eta], \[Xi], \[Phi]], a_] := (
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Eta]] GD[\[Eta]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Xi]] GD[\[Xi]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Phi]] GD[\[Phi]v, a]
);


expr = (
	\[ScriptCapitalK]d[3][1, 2][bosAns] 
	/. {\[CapitalDelta][_]|r[_] -> 0}
	/. (\[Theta]m|\[Theta]p)[_][_]:>0
	(* /. (g^(0,0,1))[\[Eta],\[Xi],\[Phi]] \[Rule] 0 *)
) // GExpand // Collect[#, f_[\[Eta], \[Xi], \[Phi]], Simplify] &


expr /. restore // Simplify


DSolve[(2 \[Phi] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+(1+\[Xi]-\[Phi]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+\[Eta] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])==0, f[\[Eta],\[Xi],\[Phi]], {\[Eta], \[Xi], \[Phi]}]


-((-1-\[Xi]v-\[Phi]v)/Sqrt[\[Phi]v]) // FullSimplify[#, x[1][1]^2+x[1][2]^2 > 0] &
\[Eta]v/Sqrt[\[Phi]v] // FullSimplify[#, x[1][1]^2+x[1][2]^2 > 0] &





(* ::Subsection:: *)
(*Invariant intervals Line defect*)


(* ::Text:: *)
(*Invariant respect covariant derivatives*)


SetNumeric[a];
Clear[y, yt];
y[i_][\[Mu]_]  := x[i][\[Mu]] - 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
yt[i_][\[Mu]_] := x[i][\[Mu]] + 1/2 Sum[\[CapitalSigma][\[Mu]][\[Alpha], \[Alpha]d] \[Theta]m[i][\[Alpha]]\[CenterDot]\[Theta]p[i][\[Alpha]d], {\[Alpha], 2}, {\[Alpha]d, 2}];
Join[
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][y[1][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]pd[\[Alpha]][1][\[Theta]p[1][\[Alpha]d]], {\[Alpha], 2}, {\[Alpha]d, 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][yt[2][\[Mu]]], {\[Mu], d}, {\[Alpha], 2}],
	Table[\[ScriptCapitalD]md[\[Alpha]][2][\[Theta]m[2][\[Beta]]], {\[Alpha], 2}, {\[Beta], 2}]
] // Flatten // DeleteDuplicates


(* ::Text:: *)
(*Invariant respect \[ScriptCapitalQ]pm[1] and \[ScriptCapitalP][3]*)


SetNumeric[kk[_]];
ansatz = (
	+ kk[1] \[Theta]p[1][1]
	+ kk[2] \[Theta]p[1][2]
	+ kk[3] \[Theta]m[2][1]
	+ kk[4] \[Theta]m[2][2]
);
ansatz = (
	+ kk[1]  yy[1][1]
	+ kk[2]  yy[1][2]
	+ kk[3]  yy[1][3]
	+ kk[4]  yyt[2][1] 
	+ kk[5]  yyt[2][2]
	+ kk[6]  yyt[2][3]
	+ kk[7]  \[Theta]p[1][1] \[CenterDot] \[Theta]p[1][2]
	+ kk[8]  \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][1]
	+ kk[9]  \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2]
	+ kk[10] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1]
	+ kk[11] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	+ kk[12] \[Theta]m[2][1] \[CenterDot] \[Theta]m[2][2]
);
sol = {};
sol = {
	kk[6] -> -kk[3],
	kk[7|12] -> 0,
	kk[3] -> -kk[8],
	kk[1] -> I kk[2]-kk[10],
	kk[4] -> -I kk[5]+kk[9]
};
{
	\[ScriptCapitalQ]pd[1][1, 2][ansatz],
	\[ScriptCapitalQ]md[1][1, 2][ansatz],
	\[ScriptCapitalP]d[3][1, 2][ansatz] 
} /. {yy -> y, yyt -> yt} //. sol  // Collect[#, \[Theta]m[_][_]|\[Theta]p[_][_], Factor] &
ansatz //. sol // Collect[#, kk[_], Simplify] &


(* // Collect[#, kk[_], Simplify] & *)


invs = {
	\[Theta]p[1][2],
	\[Theta]m[2][2],
	y[1][1]  -   \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1],
	y[1][2]  + I \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1],
	yt[2][1] +   \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2],
	yt[2][2] + I \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2],
	y[1][3] - yt[2][3] - \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][1]
};
{
	\[ScriptCapitalQ]pd[1][1, 2][invs],
	\[ScriptCapitalQ]md[1][1, 2][invs],
	\[ScriptCapitalP]d[3][1, 2][invs] 
} // Expand // Flatten // DeleteDuplicates


z1  = y[1][1]  -   \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1];
z2  = y[1][2]  + I \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][1];
zt1 = yt[2][1] +   \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2];
zt2 = yt[2][2] + I \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][2];
z3  = y[1][3] - yt[2][3] - \[Theta]p[1][1] \[CenterDot] \[Theta]m[2][1];


transRot[i__][expr_] := \[ScriptCapitalR]d[i][expr] - I \[ScriptCapitalM]d[1, 2][i][expr];
{
	transRot[1, 2][z1\[CenterDot]z1 + z2\[CenterDot]z2],
	transRot[1, 2][zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2],
	transRot[1, 2][z1\[CenterDot]zt1 + z2\[CenterDot]zt2],
	transRot[1, 2][z3],
	transRot[1, 2][\[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]]
} /. r[_] :> 0 // GExpand


\[Eta]v = (
	(z1\[CenterDot]zt1 + z2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;
\[Xi]v = (
	z3\[CenterDot]z3
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
	- 2 \[Eta]v + \[Phi]v + powerExpr[\[Phi]v, -1, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;
\[Theta]v = (
	\[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/4, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/4, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;
\[Phi]v = (
	powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2,     +1/2, \[Theta]p|\[Theta]m] \[CenterDot]
	powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;


\[Eta]v /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0}
\[Xi]v /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // FullSimplify
\[Phi]v /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // FullSimplify


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];
invAns = (
	(*+ f[\[Eta], \[Xi], \[Phi]]
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]] *)
	+ \[Eta]v
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]]
);
GD[f_[\[Eta], \[Xi], \[Phi]], a_] := (
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Eta]] GD[\[Eta]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Xi]] GD[\[Xi]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Phi]] GD[\[Phi]v, a]
);


{
	\[ScriptCapitalD]d[1, 2][invAns],
	\[ScriptCapitalP]d[3][1, 2][invAns],
	\[ScriptCapitalQ]pd[1][1, 2][invAns],
	\[ScriptCapitalQ]md[1][1, 2][invAns],
	transRot[1, 2][invAns],
	\[ScriptCapitalD]pd[1][1][invAns],
	\[ScriptCapitalD]pd[2][1][invAns],
	\[ScriptCapitalD]md[1][2][invAns],
	\[ScriptCapitalD]md[2][2][invAns]
} /. {\[CapitalDelta][_]|r[_] -> 0} /. randR // GExpand // Chop


expr = (
	\[ScriptCapitalK]d[3][1, 2][invAns] 
	/. {\[CapitalDelta][_]|r[_] -> 0}
	(* /. (\[Theta]m|\[Theta]p)[_][_]\[RuleDelayed]0 *)
	(* /. (g^(0,0,1))[\[Eta],\[Xi],\[Phi]] \[Rule] 0 *)
) // GExpand; (* // Collect[#, f_[\[Eta], \[Xi], \[Phi]], Simplify] & *)


c1 = Coefficient[expr, g[\[Eta],\[Xi],\[Phi]]];
c2 = Coefficient[expr, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]];
c3 = expr /. {g[\[Eta],\[Xi],\[Phi]] -> 0, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 0};


Sort


c1 // CollectCD[#, Simplify] &
Cases[%, HoldPattern[CenterDot[__]], Infinity] // SortBy[#, Length] &
-\[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
\[Theta]v // CollectCD[#, Simplify] &


{c1, c2, c3} /. (\[Theta]m|\[Theta]p)[_][_] :> 0


c1 \[CenterDot] c1 // GExpand
% \[CenterDot] c1 // GExpand



 


Cases[expr, f_[\[Eta],\[Xi],\[Phi]], Infinity] // DeleteDuplicates // Sort
Cases[expr2, f_[\[Eta],\[Xi],\[Phi]], Infinity] // DeleteDuplicates // Sort


expr // GExpand


expr2 = (expr /. randR) // GExpand // CollectCD[#, Factor] & // Chop


expr /. {
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] :> 0,
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 0,
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] -> 1,
	\[Theta]m[1][_] -> 0,
	\[Theta]p[2][_] -> 0,
	\[Theta]p[1][1] -> 0,
	\[Theta]m[2][1] -> 0
} // GExpand // CollectCD[#, Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &] & // FullSimplify
Solve[% == 0, \!\(\*SuperscriptBox[\(g\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]] // ExpandAll // FullSimplify


{\[Eta]v, \[Xi]v, \[Phi]v, \[Theta]v, \[Eta]v\[CenterDot]\[Eta]v\[CenterDot]\[Xi]v\[CenterDot]\[Theta]v};
 expr  /. {
	\!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]] :> 0,
	(* (f^(0,1,0))[\[Eta],\[Xi],\[Phi]] \[Rule] 0,
	(f^(1,0,0))[\[Eta],\[Xi],\[Phi]] \[Rule] 1, *)
	\[Theta]m[1][_] -> 0,
	\[Theta]p[2][_] -> 0,
	\[Theta]p[1][1] -> 0,
	\[Theta]m[2][1] -> 0,
	x[2][2] -> 0,
	x[2][1] -> 1,
	x[2][3] -> 0
	(* x[1][2] \[Rule] 0 *) 
} // GExpand // CollectCD[#, Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &] & // FullSimplify
eqs = % //. {
	x[1][1]->\[Eta] \[Phi],
	x[1][2]->-Sqrt[1-\[Eta]^2] \[Phi],
	x[1][3]->-Sqrt[-1+(2 \[Eta]+\[Xi]-\[Phi]) \[Phi]],
	\[Theta]m[2][2]\[CenterDot]\[Theta]p[1][2] -> - \[Theta] Sqrt[\[Phi]]
} // FullSimplify[#, \[Phi] > 0] &


part1 = ExpandAll[eqs] /. Complex[0,_] :> 0
part2 = I (eqs - part1) // ExpandAll // Collect[#, f_[\[Eta],\[Xi],\[Phi]], Simplify] &


Sqrt[\[Phi]] part1 // FullSimplify[#, \[Phi]>0] &


-((I Sqrt[1-\[Eta]^2] \[Theta] \[Xi] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])/Sqrt[\[Phi]])//FullForm


Solve[{x[1][1]^2+x[1][2]^2 == \[Phi]^2,
	x[1][1] == \[Eta] \[Phi]}, {x[1][1], x[1][2]}] // FullSimplify[#, \[Phi] > 0] &


Solve[((-0.7542488804229955`- 0.6844321255037191` I) g[\[Eta],\[Xi],\[Phi]]+(0.5615845786213401` +0.5059996357207578` I) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+(0.013202407892695826` -0.016405453808335926` I) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])==0, g[\[Eta],\[Xi],\[Phi]]] // Expand


inv1 = (
	(z1\[CenterDot]zt1 + z2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[1] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2] \[CenterDot] z3
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[2] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1/2, \[Theta]p|\[Theta]m]
	+ kk[3] \[Theta]p[1][2] \[CenterDot] \[Theta]m[2][2]
	\[CenterDot] powerExpr[zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2, -1/2, \[Theta]p|\[Theta]m]
) // GExpand // CollectCD[#, Factor] &;


\[ScriptCapitalK]d[3][1, 2][inv1] /. {\[CapitalDelta][_] -> 0, r[_] -> 0} /. randR // GExpand // CollectCD // Chop


%/.a->-0.0319750237819319`+ 0.17593357165724927` I // CollectCD // Chop


Solve[((-0.0008673567763213819`- 0.0018491848350067341` I)+(0.009307262479505255` -0.006621571451512355` I) a)==0, a]


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];


(* ::Subsubsection::Closed:: *)
(*Understand bosonic*)


\[Eta]v = (
	(z1\[CenterDot]zt1 + z2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify
\[Phi]v = (
	(zt1\[CenterDot]zt1 + zt2\[CenterDot]zt2)
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify
\[Xi]v = (
	z3\[CenterDot]z3
	\[CenterDot] powerExpr[z1\[CenterDot]z1 + z2\[CenterDot]z2, -1, \[Theta]p|\[Theta]m]
) /. {\[Theta]p[_][_]|\[Theta]m[_][_] :> 0} // Expand // FullSimplify


restore = Solve[{\[Eta]v == \[Eta], \[Phi]v == \[Phi], \[Xi]v == \[Xi], x[2][1] == 1, x[2][2] == 1, x[2][3] == 0}, {x[1][1], x[1][2], x[1][3], x[2][1], x[2][2], x[2][3]}] // First // Simplify


randR = Flatten @ Table[x[i][\[Mu]] -> RandomReal[], {i, 2}, {\[Mu], d}];
bosAns = (
	+ f[\[Eta], \[Xi], \[Phi]]
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]]
	(*+ \[Eta]v
	+ \[Theta]v g[\[Eta], \[Xi], \[Phi]]*)
);
GD[f_[\[Eta], \[Xi], \[Phi]], a_] := (
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Eta]] GD[\[Eta]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Xi]] GD[\[Xi]v, a]
	+ D[f[\[Eta], \[Xi], \[Phi]], \[Phi]] GD[\[Phi]v, a]
);


expr = (
	\[ScriptCapitalK]d[3][1, 2][bosAns] 
	/. {\[CapitalDelta][_]|r[_] -> 0}
	/. (\[Theta]m|\[Theta]p)[_][_]:>0
	(* /. (g^(0,0,1))[\[Eta],\[Xi],\[Phi]] \[Rule] 0 *)
) // GExpand // Collect[#, f_[\[Eta], \[Xi], \[Phi]], Simplify] &


expr /. restore // Simplify


DSolve[(2 \[Phi] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+(1+\[Xi]-\[Phi]) \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]]+\[Eta] \!\(\*SuperscriptBox[\(f\), 
TagBox[
RowBox[{"(", 
RowBox[{"1", ",", "0", ",", "0"}], ")"}],
Derivative],
MultilineFunction->None]\)[\[Eta],\[Xi],\[Phi]])==0, f[\[Eta],\[Xi],\[Phi]], {\[Eta], \[Xi], \[Phi]}]


-((-1-\[Xi]v-\[Phi]v)/Sqrt[\[Phi]v]) // FullSimplify[#, x[1][1]^2+x[1][2]^2 > 0] &
\[Eta]v/Sqrt[\[Phi]v] // FullSimplify[#, x[1][1]^2+x[1][2]^2 > 0] &



