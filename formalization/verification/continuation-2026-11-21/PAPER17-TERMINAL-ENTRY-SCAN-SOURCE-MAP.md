# Paper 17: actual terminal-inclusive entry hit/miss

**Target-only supporting packet.** No proof, new native run, or numbered
credit. This is the first closed-entry supplier for the actual finite strips,
not finite-strip substitution or the arithmetic decision theorem.

Printed source: arithmetic.tex, “Residues, finite strips, and one-variable
projection”: close the fields on a fixed low-coordinate input with
their actual values and true definedness flags. See
`PAPER17-LOW-STRIP-TERMINAL-SCAN-SOURCE-REVIEW.md` for the static route.

- **Actual input domain.** `terminalScanGuard` uses the raw normality tests
  and compares the target with the code of its own limit part.
  `TerminalEntryScanGuardExact` requires primitive recursion and exact
  equivalence with both codes decoding to normal notation and the target
  being zero or a positive successor-limit ordinal. A target with a
  positive finite tail, including a positive finite ordinal, is rejected,
  not classified as a missed valid target. Calibrate with checked raw
  normal/decode/split semantics and actual limit-part decomposition.
- **Actual inclusive prefix.** The runnable test is *literal* encoded
  state, split, and target-code equality. The finite accumulator at index
  zero tests zero, and at each successor tests that index if and only if
  nothing earlier has been retained. For every raw tuple and arbitrary
  actual control the numeric index contract says zero means every index
  through T is false; a positive code is the earliest successful index
  plus one, with the right bound and all previous failures. This internal
  zero is not a result value.
- **Total guarded program.** Invalid raw inputs return option `none`
  without entering search. Valid codes use the actual `terminalSearchWith`
  and finite accumulator, returning `some none` for a real miss or
  `some (some (norm,index))` for a hit. `TerminalEntryScanEffective`
  requires actual domain on *every* raw pair for every actual control, not
  only a Partrec claim or an on-tail totality theorem. Relative to a
  computable control it additionally requires computable prefix index,
  actual partial recursion, and computability of the definite realization.
  The latter is represented by `getOrElse none` solely to make a Lean
  function before proving domain; the target requires that divergence
  fallback never be taken. No invalid or miss branch returns a norm.
- **Actual iff and endpoint.** `firstFinite_correct` supplies the terminal
  index on normal starts. `entry_test_iff` converts each code predicate
  to the actual entry interval, and `firstEntry_le_terminal` is essential
  for absence and the reverse hit direction. Use trajectory calibration
  through the terminal index for the exact norm and count, not equality of
  encoded/actual states after termination. Exact hit iff and miss iff are
  required, not only successful hit soundness. Zero target requires
  precisely the terminal pair, including index zero for already finite
  starts.
- **Outside this freeze.** No fixed endpoint lambda/mu/t lift, no
  affordability or identity-call convention changes, no generic
  high-tail-to-low substitution, no raw coordinate strips or count bridge.
