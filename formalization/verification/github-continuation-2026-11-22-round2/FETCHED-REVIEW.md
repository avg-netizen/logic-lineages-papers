# Rounds 3–5 source review — 22 November 2026

Reviewed head: `b28541e6f1682fc41c47a385729df36e9db87b0d`, following the
round-2 review at `fd88501ef35c0f347fc754f72d93a1088c733c9f`.

The fetched work adds 487 Lean modules and supporting records #1450 and
#1452–1473. Record #1451 promotes Paper 17's principal theorem. The current
register is **160 checked / 7 pending / 167**, with every pending statement in
Paper 16. This continuation preserves those numbered statuses and the manuscript.

## Findings that determine this continuation

### Preserve the explicit family in the uniform main theorem

The effective main endpoint #1471 retains the literal `sequenceTerm` witnesses
and their strict cofinality. The uniform-accessibility endpoint #1473 instead
concludes the older `Main16Statement`; it does not include that explicit family.
Both accepted implications are correct as stated, but no single one of those
endpoints retains both improvements. The new `ConditionalMain16UniformEffective`
target composes the existing uniform-to-individual accessibility bridge with
#1471. Its five hypotheses are unchanged.

The coding integration strengthens this combined conclusion further. Its
`CodedEffectiveCofinalFamily` requires the same closed native terms, their literal
syntax, their existing numerical codes, strict cofinality, all family ranks below
BH, and nonattainment of BH by an ordinary term's full confined rank. It also
asserts primitive recursiveness of the particular code generator. No coding
supplier is added to the main theorem's hypotheses.

### Formalize numerical effectiveness of the actual tower family

The scope notes for #1470/#1471 correctly distinguish the explicit, choice-free
syntax recursion from a theorem of `Primrec` or `Computable` on numerical codes.
The old `EffectiveCofinalFamily` fixes the syntax witnesses but contains no such
computability predicate. This is a genuine remaining clause of the printed
principal theorem's effective-family requirement.

The new `NativeTowerCode` packet addresses precisely that clause. Its natural
code generator follows the literal tower constructors and is compared with the
existing `tr` and `encodeTerm`, hence with the existing `nativeCode`. The frozen
calibration target requires successful translation to `some (sequenceCode n)`;
the default-zero branch of `nativeCode` cannot stand in for this result. The
primitive-recursive claim concerns syntax generation, not rank computation or
an algorithm selecting a cofinal witness from an arbitrary ordinal.

See [the coding source map](tower-code/SOURCE-MAP.md) and the
[independent source comparison](norm-interface/TOWER-CODE-SOURCE-REVIEW.md).
Proof validity and acceptance are recorded separately after the native gate.

### Separate full type calibration from accepted-address calibration

The exact #1464 targets distinguish `AllTypesWindowed s` from
`AcceptedTypesWindowed s`. The former requires every valid type code to lie in
a finite window; the latter concerns only types of addresses accepted by the
original scalar. The round-4 prose compresses these two questions when discussing
the installed tuple.

The tuple's actual condition is `ActualTypeGuard`, an equation with `typeBit`
on **every** natural input. A refitted checker contains the literal finite
membership check `grammarTypeAt s`. The new type-boundary targets construct
unbounded valid arrow codes directly for the original `typeTable`, obtain a
valid code outside every finite list, and show that the refitted checker cannot
satisfy `ActualTypeGuard` or occupy that slot of `InstalledTupleAt`. These
impossibility targets require no calibration of either component checker.

This does not refute `AcceptedTypesWindowed`, prove internal nonderivability,
or discharge the original application's type guards. The numeric arrow law and
the original object-calculus derivation rules remain separate. See the
[type-boundary source map](type-boundary/TYPE-BOUNDARY-SOURCE-MAP.md).

There is also a direction typo in the frozen round-4
`fable2/REFITTED-INSTALL-SOURCE-MAP.md`: the displayed equivalence is
`ActualScalarCalibration ... ↔ AcceptedTypesWindowed s`. The window condition is
consumed **right to left** to recover scalar calibration and derived **left to
right** from calibration. The exact Lean target has the correct orientation.
This erratum preserves the historical source map's pinned bytes.

## Other source conclusions

The finite-chain realization additions #1450/#1452 supply the printed proof's
finite beta-chain transport. They do not turn the one-binder abstraction rule
into a general typed lambda fundamental lemma. The realization wording decision
remains open; the proposed manuscript edit is not applied here. The earlier
positive source comparison for `thm:iteration` is unchanged, and its numbered
promotion remains a separate decision.

The norm and accessibility interfaces use derivability from the **empty logical
assumption list**. Their numeric source/context parameter is not a logical
assumption context. The scalar evaluation calibration also fixes the original
checker at every input. No arbitrary logical assumptions or empty-domain choice
are silently used to obtain the conditional ordinal conclusions.

The conditional height/main family still depends on all five named hypotheses:
the ID₁ norm theorem, uniform internal accessibility, Simmons calibration,
the tower/collapse hypotheses, and identification of the endpoint with BH.
The toy model #1469 establishes consistency of the abstract tower bundle only;
it does not instantiate those hypotheses for the paper's intended collapse.
The new code theorem is independent of those hypotheses, while its cofinal-rank
integration retains them.

## Evidence checked

[FETCHED-CHECKS.json](root/FETCHED-CHECKS.json) records the reviewed commit,
changed paths, current register, and published evidence checks. The fetched
delta has 656 files, including 475 new native-module files and 12 other new Lean
files; no pre-existing Lean source changed. All 23 supporting evidence digests
and their current Lean source pins match. Their 53 named axiom summaries contain
only `propext`, `Classical.choice`, and `Quot.sound`.

These checks use the published evidence summaries and source bytes. They do not
claim a replay of the authoring host's historical full native receipts. Fresh
focused native gates validate this continuation's new endpoints and their actual
dependency closure. The completed results, exact receipts, failures and repairs
are reported in this checkpoint's acceptance evidence and final handoff.
