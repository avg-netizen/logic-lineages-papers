# Internal induction over the original list codes

This component supports paper 06, `lem:id1` (the arithmetic accessibility
argument), especially its finite-multiset and finite-certificate reasoning.
It does not complete that lemma. The source constructor, lambda,
computable-substitution and all-term accessibility arguments remain separate.

## Full-language strong induction

`InternalStrongInductionTargets.ActualStrongInductionSchema` uses the original
`InternalCalculus.Derivation` and the original arithmetic strict-order formula.
For an arbitrary formula `theta`, it derives

    [forall n, ((forall m < n, theta(m)) -> theta(n))] -> forall n, theta(n).

The invariant may contain arbitrary occurrences of the one inductive
predicate, including negative occurrences, and arbitrary free parameters.
The contextual rule retains the original hypothesis list; the instance rule
allows any symbolic arithmetic term. The proof uses the existing full-language
least-number theorem and explicit double-negation elimination in the same
calculus. There is no semantic truth-to-derivability step.

## Literal list-code induction

`InternalListInductionTargets.ActualOriginalListInduction` proves the actual
first-order schema

    [theta(0) and forall n h t,
       (Graph(consCode, n, [h,t]) -> theta(t) -> theta(n))]
      -> forall n, theta(n).

`consCode`, `headCode` and `tailCode` are the recovered original programs.
The cons graph is the original graph compiler applied to successor of the
original natural pairing program. The result covers all natural codes;
there is no premise saying the input is canonical or has already decoded.

For a nonzero symbolic code, original program totality supplies its head and
tail inside the object calculus. The recovered reconstruction proof supplies
the literal cons graph, and its recovered descent proof makes the tail
strictly smaller than the code. Strong induction then supplies the tail
invariant and the original constructor premise supplies the code invariant.
The zero/nonzero split is an object-calculus classical proof. All witnesses
are discharged by the original existential rule.

## Exact original parser

`NumberedMultisetNumericTotalityTargets` refers directly to the existing
`NumberedMultisetNumeric.numbersParse`, `decodeNumbers`, and `numbersNumber`.
No parser or encoding definition changes. The six targets prove parser
totality for `value < fuel`, unique decoding of every natural, bijectivity of
the original encoding, the exact decoding equation, length and entry bounds,
and the sharper exact fuel criterion

    numbersParse fuel value = some xs
      iff numbersNumber xs = value and xs.length < fuel.

The strict length bound accounts for the final nil inspection. These are
natural-list facts, not a claim that every number is a valid typed term,
multiset certificate or reduction-path certificate.

## Scope

The three components add eleven fixed supporting targets. The numbered
statement register remains 168 checked, 2 inherited and 19 pending out of 189.
The original arithmetic and source definitions, recovered source bytes,
compiler resource limits and dependency pins are preserved.
