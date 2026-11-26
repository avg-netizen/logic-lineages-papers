# Paper 17: exact fixed-entry closed scan

**Target-only successor to the checked terminal-inclusive scan (720).**
No new proof/native evidence, owner code or numbered credit.

Printed scope: the underlying fixed entry calculation for later exact
small-input substitution in arithmetic.tex (“Residues, finite strips,
and one-variable projection”). The source domain guard of an *outer call*
is distinct from this underlying calculation.

- **Literal lift:** input tuple is `(raw λ, raw μ, t)` in the original
  `FixedEntryProgramDefinitions` order. Use
  `canonicalInitialCode λ t` and the exact accepted
  `terminalEntryScanProgram` at `(canonicalInitialCode λ t, μ)`.
  Check raw λ normality *before* forming a scan branch, since a malformed
  λ is not admissible even if numeric endpoint arithmetic returns a
  valid notation. The three statuses are unchanged: invalid, genuine
  miss, and hit carrying only the exact norm/index.
- **Raw totality/effectivity:** pair constructor is required primitive
  recursive; the literal guarded partial program has actual domain on
  every raw input for every actual control. For computable controls it
  and its definite realization must be Partrec and Computable,
  respectively. The getOrElse representation is not a substitute for
  that domain proof. The invalid status is exact on arbitrary raw
  triples, with normal-input and zero-or-limit-target characterization;
  the valid-λ branch literally agrees with the accepted scan.
- **Actual semantics:** for every actual normal λ, actual normal
  zero-or-limit μ and **every natural t**, use the checked
  `canonicalInitialCodeCorrect` (normality and repr) to transfer the
  exact FirstEntry/norm and genuine no-hit iff to the original
  `countInitial λ t`. No t bound, no selected-control restriction,
  no assumption that a hit exists. `FixedEntryClosedOriginalGraph`
  matches the original fixedEntryProgram result graph under its real
  computable-control hypothesis; it does not claim that old partial
  search becomes total on misses.
- **Outside this freeze:** later validate actual affordability,
  endpoint/identity-call conventions, ordinary-field and count wrappers,
  and whole infinite-strip substitution with common-coordinate sharing
  and exact domain flags. In particular truncation inside
  `countInitial` below the source norm is not a license to accept an
  unaffordable source call. No printed theorem or register promotion.
