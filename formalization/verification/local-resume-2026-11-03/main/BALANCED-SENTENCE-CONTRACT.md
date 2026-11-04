# Balanced comparison sentences: source contract for the next main-thread component

Status: source contract only. No new Lean target, proof, compilation or acceptance
is claimed by this note. The arithmetic decision supplier remains unpaid.

## Source and current checked supplier

Paper08 begins with positive-natural raw source variables. Its `thm:common`
and `thm:balanced` promise translation of pointwise comparisons to the ordinary
first-order structure (Nat;0,1,+,<,Phi), retaining original free variables,
followed by arbitrary Boolean and quantified combinations. The balanced
finite-box argument explicitly uses [1,L-1] on the actual source support.

The fetched `BalancedExactVariables` development already supplies:

- `sourceFormula Gamma C E F desired` in actual ordinary BASE syntax;
- exact source-sign semantics when the original certificate/expressions are
  genuine and the valuation is positive on the ORIGINAL pair support;
- exactly the original variable-set membership even after complete cancellation;
- literal code calibration and an all-code Computable wrapper.

See `BalancedExactVariablesTargets.lean`, its unchanged StatementChecks gate,
and the November3 external STATUS/register coverage. No independent basis
values or raw input aliases may be introduced by the next component.

## Required sentence semantics

Use literal named-variable first-order syntax with the same raw Nat names.
Each comparison atom retains its own entire actual common certificate, pair of
expressions, shape and desired sign. A sentence may combine differently shaped
certified atoms; every atom's genuine-domain condition must be explicit.

Interpret source quantifiers over POSITIVE raw naturals, consistent with the
source domain. Translate into ordinary Nat quantifiers using literal BASE
positivity guards:

- exists x over positive naturals becomes exists x (0<x AND translated body);
- forall x over positive naturals becomes forall x (NOT(0<x) OR translated body).

Source negation, conjunction, disjunction and any derived connectives keep their
ordinary logical meaning. Bound-variable updates must occur under the SAME raw
valuation, and nested binders may reuse/shadow a raw name. Distinct atom supports
remain their actual supports; they do not become fresh independent parameters.

Pointwise correctness should require positive values only for the sentence's
FREE raw variables. A proof by syntax induction must derive each bound-variable
positivity condition from its guard, rather than assuming positivity of every
Nat-valued assignment or a bound-variable-independent source atom.

## Exact prospective targets

1. Literal embedding of quantifier-free BASE formulas into the quantified BASE
   syntax preserves interpretation and free-variable membership.
2. The constructed translation of arbitrary source comparison formulas preserves
   truth at every source-positive FREE valuation, with genuine certificates at
   all source leaves. This must include negation and both quantifier directions.
3. For every raw name, membership in the output's FREE variables is exactly its
   source membership. Positivity guards introduce only the bound name, and its
   binder removes it. Empty support and cancelled comparisons remain covered.
4. The actual output-code construction is total Computable under the explicit
   input coding. Reuse the paid comparison-code function; do not supply a formula
   selector or correctness oracle, or conclude computability from a noncomputable
   syntax definition alone. A semantic-only intermediate must say so explicitly.

Examples to retain include a variable present only in a cancelled source pair,
negated comparisons, a quantified name also free elsewhere in a conjunction,
shadowing of a binder, and an atom with empty original support. Ordinary Nat
quantification WITHOUT the 0<x guards is a different domain and is not silently
identified with the source-positive claim.

## Completion boundary

These are translation suppliers for paper08's `thm:balanced` and reusable for
`thm:common`. They do not themselves decide first-order arithmetic with Phi.
Full source promotion still needs the genuine Snyatkov procedure and its entire
proved dependency chain, plus final effective sentence-decision assembly.
No solver may be hidden as an assumption or an abstract class field.

Main reserves NEW BalancedSentence* files. L3 independently owns SnyatkovInverse*
and the genuine arithmetic supplier chain; L2 owns termination-ordering effects.
All accepted sources, comparison types, manuscripts and code interfaces remain
unchanged by this preparatory contract.
