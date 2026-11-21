# Paper 17: exact low-strip terminal scan (source review only)

**Unproved proposal.** Read the manuscript and live Lean sources in
owner baseline `762b1c9122ede8c5b752e0be277ff7657f30f099`. No Lean
target, proof, checker run, or native gate was added; no accepted status
changes. This is a closed-evaluation supplier for the genuine finite
strips, not order normalization or the printed arithmetic theorem.

## The literal finite search

`EvaluatorDefinitions.lean` already defines
`terminalSearchWith f code = Nat.rfind (fun k => Part.some
(encodedFiniteTest (encodedStatesWith f code k)))` for the actual
encoded trajectory. On a normal start code `n = rawNoteEncode a.1`,
`EncodedEvaluatorProof.firstFinite_correct` proves its actual answer
`T = (terminalWith f a.1.repr).2`, with the actual finite value.
`TerminalProof.terminal_firstFinite` proves that no earlier state is
finite. This proof of the search's domain needs neither a guessed fuel
nor any affordable-tail or comparison-threshold premise. The effective
supplier is the existing computable encoded-state function with the
checked finite test. `evaluator_partrec` uses the resulting
`Partrec.rfind` proof locally; the short partial-recursiveness proof
for `terminalSearchWith` can be supplied explicitly in the new packet.

After obtaining that actual `T`, scan **every index 0 through T,
inclusive**, in increasing order, testing the exact old predicate:
```
(rawSplitCode (encodedStatesWith f n i)).unpair.1 == targetCode
```
Return the first hit `(rawNormCode (encodedStatesWith f n i), i)`,
or a genuine no-hit status. A finite accumulator can keep the first
result once found. An equivalent effective bounded search can use a
sentinel hit at `T+1` distinct from any admissible hit. Neither approach
runs the possibly divergent old entry search and then fabricates a
fallback.

The two post-terminal facts must remain distinct:
- `EntryBasicsProof.encoded_after_terminal_fixed`: the finite **code
  is absorbing**, so every encoded state at or after T is exactly the
  same finite code.
- `EntryBasicsProof.descent_finite` and
  `actual_after_terminal_finite`: actual ordinal `descentWith f`
  sends a finite value to **zero**, but remains finite. Equal ordinal
  states or equal norms after T are not implied by code absorption.
- `EntryBasicsProof.firstEntry_le_terminal`: each genuine first entry
  into a zero or limit target interval has index at most T. A positive
  limit cannot be reached after T; for zero, T already hits. This is why
  scanning only through T is exact, and why excluding T would lose the
  terminal zero-target hit.

## Proposed exact contracts and domains

On arbitrary actual normal start `a`, normal target `mu` with
`mu.repr = 0` or `IsSuccLimit mu.repr`, and the actual control:
1. The proposed closed routine is uniformly computable on natural codes
   for each computable control. Branch on the checked normal-code test
   before running the terminal search; `rawNormalDecodeCorrect` and
   `rawNoteEncodeDecode` cover every admitted raw start. A public
   selected-control specialization should retain the actual
   `factorialControl` and `nearControl b`, not a replacement model.
2. A hit `(E,i)` occurs iff `FirstEntry f a.repr mu.repr i` and
   `E = entryNormAt f a.repr i`; genuine no-hit occurs iff no such
   first entry exists. `EntryEffectivityProof.entry_test_iff` pays the
   exact numerical predicate versus the ordinal interval; leastness
   and the terminal bound close both directions. Calibrate the returned
   norm using `trajectory_correct` only through T and the checked raw
   norm correspondence. The hit graph also agrees with the old partial
   entry program by `entry_search_iff` / `entryEffectivity`; a miss is
   certified by absence of any old result, not by waiting for one.
   If `mu = 0`, the returned pair is exactly `terminalWith f a.repr`.
3. Lift to fixed entry `(lambda,mu,t)` with
   `canonicalInitialCodeCorrect` and the exact old
   `fixedEntryProgramEffectivity` graph, at **every natural t**, not
   just `t >= max {2,N(lambda),N(mu)}` or above the solver cutoff.
   This underlying calibration applies to the actual `countInitial`
   convention. An outer circuit must still impose its *true* source
   guard (e.g. `t >= N(lambda)` for unshifted raw input). The subtraction
   inside `countInitial` truncates; it does not license answering an
   unaffordable source call. Test proper endpoints as required, and keep
   the separate identity convention `E=t, count=0`.
4. Distinguish malformed code or failed source domain from a valid
   skipped entry: use distinct statuses or separately exact rejection
   flags. A positive finite target is not in the zero-or-limit
   calibration: `a=mu>0` finite lies in its interval but its limit
   part is zero. Do not label such rejected inputs genuine misses
   under `FirstEntry`. Neither an invalid input nor a miss returns a
   fabricated numeric zero.

For the **fixed-head collapse** gate, the already checked closed
evaluator takes the literal normal ordinal for `alpha+u`, which can be
formed by effective ordinary ordinal addition. A finite head gives
`alpha+u` directly; an infinite `alpha=lambda+k` gives a
`J_lambda` norm input `N(lambda)+k+u`. This is different from a
finite extension below `N(lambda)` of the unshifted *raw norm input*
function. The latter is allowed only when explicitly specified as
computable finite cases in the source, never as an implicit extension
for failed entry guards. On actual hit fields use the genuine returned
norm/count and then the requested control iterate; do not apply a
high-tail short-field rewrite to a low input without its hypotheses.

## What this would pay downstream

Paper 17 `sections/arithmetic.tex`, “Residues, finite strips, and
one-variable projection”, fixes one permitted below-cutoff coordinate
at a time. Evaluate the fields on that coordinate exactly, substitute
the **same** value at every occurrence and shared circuit node, and
retain all earlier domain/definedness guards, including guards outside
negated output tests. The other coordinates stay unbounded. These are
potentially infinite strips, not a bounded cube; recursive
smaller-dimensional coverage and compilation remain separate.
