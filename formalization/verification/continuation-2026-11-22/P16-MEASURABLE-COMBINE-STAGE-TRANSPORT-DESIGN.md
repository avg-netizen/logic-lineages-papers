# Paper 16: chosen measure combine and cross-bound stage transport

Design only. No Lean candidate, gate, acceptance, or new unconditional claim.

## One physically chosen measure combine

`NumberedWindowInternalAuxMeasureMemoTargets.combine` is precisely
`encode (auxiliaryMeasure (readMeasure mf) (readMeasure ma))`. For the
pinned `Encodable (Nat × Nat)`, `encode_prod_val` with `encode_nat`
identifies the unshifted standard `Nat.pair`, and `decode_prod_val`
with `decode_nat` gives `some n.unpair` for every natural input n.
Thus the `getD (0,0)` is unreachable here; zero is the valid pair
(0,0), not None/Some or a sparse cons tag.

On literal tape [mf,ma], select two calls to `InternalUnpair.left`, two
to `InternalUnpair.right`; compute
`d = addition left(mf) left(ma)` and
`b = branch ltTest (projection 0) (projection 1) [right(mf),right(ma)]`.
The output is actual `InternalPairing.pairing` applied to `[suc d,b]`.
Freeze all-input `CombineCalibrated` for this very AST, using
`exactUnpairEvaluation`, `exactPairingEvaluation`,
`exactAdditionEvaluation`, `exactLessThanEvaluation`, and `evalBranch`.
The previous `OriginalBoundsRecombination.ArithmeticProof.maximumValue`
has the identical max pattern (not a necessary import); its `merge`
does **not** add the auxiliary successor and is not this combine.

Freeze an independent open rule: given actual child pair graphs with
coordinates (df,bf) and (da,ba) and the actual chosen-combine output p,
construct one object existential b with actual pair graph
`pairing p [suc (add df da),b]` and actual order formulas
`ltF df (suc (add df da))`, `ltF da (suc (add df da))`,
`ltF bf (suc b)`, `ltF ba (suc b)`. These express inclusion into
the parent **predecessor** depth and its numeral bound. The original
generated-code inverse gives child coordinates; use genuine
`compositionRecover`/ `compositionValue`, `additionValue`, and
`successorValue`, actual order cases and `acceptOfLess` /
`rejectOfNotLess` with branch graphs (tie chooses first), and
`leftWeakAdd` / `rightWeakAdd` for the depth inequalities.
For max weak bounds use strict/equality order split plus right-successor
order, not a numerical reflection rule. Where arbitrary child codes are
not already supplied with coordinates, actual left/right graph cases
and `actualOriginalUnpairReverseInverse` supply the actual pair graphs;
no semantic decode assumption is needed. Keep that extension separate
if the first open target is cheaper with pair reports as hypotheses.

Select this exact combine P in `measureUpdate base P`; the prior
`exact_PhysicalAuxMeasure` pays numerical selection and
`exact_OpenAuxMeasureEvaluation` (#858) pays the same child's actual
P report to the actual parent's M report. Neither theorem proves
the coordinate inequalities for an arbitrary old P, nor transports
any grammar occurrence.

## Transport of genuine occurrences across original grammar bounds

Keep one H,K; do not derive membership from equal outputs (lists at bigger
bounds need not be equal or even insert their entries only at the end).
The useful target is two-way-component **forward inclusion** only:
for actual grammar state reports at (d,b) and (D,B), with genuine
`ltF d (suc D)` and `ltF b (suc B)`, transport an actual term
occurrence, or an actual argument-list occurrence, to the respective
component of the larger physical report. Same candidate, same H,K, no
sortedness, duplicate removal or output-list equality.

First pay two simpler physical transports, then compose them:
1. Same numeral bound, one successor of depth. Simultaneously maintain
   term and argument occurrence inclusion. At depth zero, terms are empty
   and argument list contains the actual 0 sentinel; the next argument
   stage also has that sentinel. The paired recursion then lifts the
   preceding inclusions through each constructor's actual axes.
2. Same depth, increasing numeral bound. Simultaneously recurse over the
   same depth. Pay inclusion for actual numeral-axis range through the
   larger bound (`range (b+1)` includes b). Reuse the stage-local
   component lifts; iterate successor rules internally or prove the
   direct weak-order form using actual arithmetic/list induction.

Reuse #881's actual Cartesian application membership and #882's
successor auxiliary introduction; use the narrow actual append
preservation only after its gate. These pay the tag-six branch, not
backward inversion of every stage output. Actual stage transport needs
both output membership decomposition and input occurrence transport for
the non-auxiliary prefix (leaves, lambdas, ordinary, numbered) and
nextArgs `cells`. The `LayerPartsCalibrated P A` used by #882 only
pins standard evaluation; the previous `chooseLayerParts` supplies
existentially compiled callbacks. In particular its opaque P/A do not
supply those object rules. Either explicitly pay the named local laws
as conditional premises, or select literal physical range, axes, and
cells programs with separate numeric calibration and internal constructor
graphs. The grammar's argument cell construction uses the sparse
polynomial pair plus one; do not replace that inner cell by the
standard scratch cons/pair, which is used only to store ordered lists
or the two grammar stage outputs. External monotonicity of `grammar`
as membership/subset is a separate lightweight theorem, not open
transport or a substitute.

Finally, given actual child own-cover term-list reports and occurrences,
use chosen measure inequalities to transport both children to the
parent predecessor depth and parent numeral bound. Use the newly
selected fixed grammar type guard only once its physical callback
occurs in the relevant proof. Then combine the open parent own-cover
rule with these paid transports. Child own-cover premises, the exact
application installation, and any unconditional all-address result
are still separate.
