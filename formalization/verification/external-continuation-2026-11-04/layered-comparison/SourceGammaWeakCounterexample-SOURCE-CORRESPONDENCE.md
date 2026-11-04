# Exact computable failures of independent weak comparison

Paper09 hardness.tex lines 316–319 enumerates positive raw ground tuples to semidecide failed universal comparison. This component establishes only the weak counterexample predicate and its exact existential witness equivalence, not the search or classification.

The language is the unchanged independent SourceGammaWeakCodedReduction.Member. A successful pair of finite observations left=x, right=y violates weak order exactly when y<x. The predicate uses strict right<left, unlike the strict-language failure test right≤left. This comparison orientation is stated explicitly in ExplicitFailures.

The independent restricted syntax checker is evaluated first: an invalid syntax code immediately yields true, since it is outside Member. A subsequent failed tuple decode yields false and is impossible for successful syntax. The list must have exactly the decoded context length and positive entries. A missing result from either actual fixed-Gamma evaluator yields false, never a false counterexample certificate. Accepted typed restricted-source totality handles valid inputs. Existing full positive-list coverage, not just one-way interpretation, proves completeness of witnesses.

The function is Computable jointly in query code/list for each fixed b. No joint-in-b or primitive-recursive evaluator claim is made. ExactCounterexample concerns every natural query code, including malformed codes, with no generated-range restriction. No rfind, RE complement/classification, runtime, weak source theorem/register promotion or export is asserted.
