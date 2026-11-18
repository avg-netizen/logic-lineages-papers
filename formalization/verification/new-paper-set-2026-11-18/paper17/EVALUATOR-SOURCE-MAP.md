# Evaluator frozen source map

`descentWith f alpha` is the printed nonfinite replacement with the limit
part as the first M argument, original state's exact norm in the budget,
and f left arbitrary. The actual `terminalWith` is independent ordinal
well-founded recursion; its stored pair is (first finite endpoint,event count).
A finite input returns its own value and zero events. Its structural recursive
proof uses actual maximum correctness and the nonzero limit decomposition,
not supplied termination evidence or the numeric search.

`encodedStepWith` uses the same limit-part/norm budget on faithful raw codes;
finite states are absorbing. `encodedStatesWith` performs k steps.
`terminalSearchWith` is Nat.rfind of the finite-state test, hence membership
states that k is the first successful index. The partial program maps this
index to the exact finite value plus count and handles invalid normal-form
codes immediately. The getOrElse wrapper does not imply totality.

`TerminalSemantics` includes actual first-finite denotation, nonfiniteness at
every earlier index, independent collapseWith decomposition, exact f-iterate
norm orbit and 0<D<Z for every nonfinite start. `EffectiveEvaluation` separately
requires that this actual semantic count belongs to the concrete least search,
that its finite value is the semantic endpoint, actual Partrec, totality on
every natural code, Computable of the wrapper, and denotation equality on every
normal notation. Thus neither a semantic-only result nor mere search success
with an unspecified witness can fulfill the frozen target.

`ComputableEvaluation` retains the source generic per-function Computable f,
StrictMono f and G-majorization assumptions. There is no uniform higher-order
index claim. `SelectedClosedEvaluation` removes all those premises for the
actual factorial control and every nearControl b, using their independently
proved primitive-recursive and numerical laws. No joint-in-b computability
claim is made. The separate optimized simultaneous M/L algorithm and later
residue/count/comparison theorems are excluded.
