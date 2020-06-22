(* ::Package:: *)

Quit


Clear[\[Delta], der, i, j, w, xy, q];
der[a_Plus, x_] := der[#, x] & /@ a
der[a_ b_, x_] := a der[b, x] + b der[a, x]
der[w[i_], w[j_]] := \[Delta][i, j]
der[\[Delta][__]|q|q^a_|xy|xy^a_, _] := 0
der[num_?NumericQ, _] := 0

SetAttributes[\[Delta], Orderless];
\[Delta] /: \[Delta][a_, b_] \[Delta][b_, c_] := \[Delta][a, c]
\[Delta] /: w[a_] \[Delta][a_, b_] := w[b]
\[Delta][i[a_], i[b_]] := 1
\[Delta][i[a_], j[b_]] := xy
\[Delta][j[a_], j[b_]] := 1

DOrth[i_, q_][expr_] := With[{j = Unique[]},
	((q-2)/2) der[expr, w[i]]
	+ w[j] der[der[expr, w[i]], w[j]]
	-1/2 w[i] der[der[expr, w[j]], w[j]]
] // Expand;

Table[
	lhs = 1 / (s! Pochhammer[q/2-1, s])
		Fold[DOrth[i[#2], q][#1] &, Times @@ (w /@ j /@ Range[s]), Reverse@Range[s]] //
			Expand // Collect[#, xy, Factor] &;
	rhs = 2^(-s) Binomial[s+q/2-2, q/2-2]^-1 GegenbauerC[s, q/2-1, xy] // FunctionExpand;
	lhs - rhs // Together
, {s, 1, 8}]
(* FindSequenceFunction[%][ss] *)
