# Checked GitHub continuation — 22 November 2026, second round

**Completed:** four supporting packets, **16 exact checked endpoints in nine new
Lean modules**, following the fetch and source review of rounds 3–5 at
`b28541e6f1682fc41c47a385729df36e9db87b0d`.

The current branch is `formalization/github-measured-install-2026-11-22`.
Source checkpoint `5d3f9d9206d3c1dc417d4f7a1e6bc7a7b08873f7` preserved the
frozen specifications and pending proof candidates. This handoff accompanies
the completed proofs, retained failed drafts, acceptance records and portable
native evidence. The user authorized committing and publishing the finished
continuation on the same branch.

The numbered register remains **160 checked / 7 pending / 167**. Paper 17 remains
complete in the register; every pending statement is in Paper 16. No manuscript
or numbered status changed.

## Checked mathematical additions

| Record | Exact contribution | Boundary |
| --- | --- | --- |
| [#1474](../new-paper-set-2026-11-18/accepted/1474-p16-uniform-effective-main.json) | Combines the uniform closed-theory accessibility input with the explicit cofinal native family retained by #1471. | The same five ordinal/accessibility hypotheses remain. |
| [#1475](../new-paper-set-2026-11-18/accepted/1475-p16-refitted-type-boundary.json) | Original numeric type-test arrow law, unbounded valid type codes, finite-list omission, and unconditional impossibility of an actual installed tuple using the refitted checker. | Numeric and installation-boundary facts; no internal guard discharge or refutation of accepted-address calibration. |
| [#1476](../new-paper-set-2026-11-18/accepted/1476-p16-primitive-recursive-tower-code.json) | Unconditional `Primrec` and `Computable` generation of the actual tower syntax codes, with successful translation and existing-`nativeCode` calibration. | No claim that ranks or ordinal cofinal-witness selection are computable. |
| [#1477](../new-paper-set-2026-11-18/accepted/1477-p16-uniform-coded-effective-main.json) | The uniform conditional main theorem retains the same literal closed native witnesses and their actual primitive-recursive codes, together with cofinality and height. | Coding is supplied by #1476; all five existing ordinal/accessibility hypotheses remain uninstantiated. |

### Actual tower codes

`NativeTowerCode.sequenceCode` is a natural-number program following the actual
finite-type tower constructors, binders and descending application spines. It
uses the existing polynomial pairing and constructor encoding. The exact results
include:

```lean
Primrec sequenceCode
Computable sequenceCode
∀ n, literalCode (sequenceTerm n) = some (sequenceCode n)
```

Here `literalCode q` is exactly `(tr q).map encodeTerm`. The successful `some`
equation rules out a fallback-zero interpretation. A further theorem proves
`nativeCode t = sequenceCode n` for every actual closed native representative
whose syntax is `sequenceTerm n`; no new encoding instance on `Expr` is required.

The coded main theorem retains items 1–5, the ordinary-term upper bound, height
equality and the literal closed-native family. Its ranks are strictly cofinal in
BH and individually below BH; no ordinary term's full confined rank is BH.
The generator and its calibration are conclusions supplied by the unconditional
coding theorem, not additional hypotheses.

### Why the finite refitted checker cannot be the actual type checker

The original `typeBit` accepts the explicit chain
`a₀ = 0`, `aₙ₊₁ = arrow 0 aₙ`, and `n ≤ aₙ`. Thus valid codes are unbounded,
and every finite list omits one. The literal `grammarTypeAt s` membership
conjunct rejects a valid code outside `s.types`; so do `refitGuard s T` and
`refittedScalarType s TV T`, for arbitrary component programs.

Consequently, **no** finite refitted scalar type checker satisfies
`ActualTypeGuard`, and no `InstalledTupleAt` can contain it in that slot. Unlike
#1464's necessary-condition theorem, these impossibility results require no
`TypeGuardCalibrated`, `GrammarTypeInclusion` or calibration of `TV`.

When `TV` itself has the actual all-code calibration, a separate theorem gives
an accepted arrow, accepted domain and accepted codomain whose codomain is
rejected by the refit guard. This is a numeric counterexample, not an assertion
of internal nonderivability for an arbitrary object-calculus body. The separate
`AcceptedTypesWindowed` condition for types of accepted addresses is not refuted.

## Review of the fetched work

[FETCHED-REVIEW.md](FETCHED-REVIEW.md) and
[FETCHED-CHECKS.json](root/FETCHED-CHECKS.json) record the source assessment.
The fetched delta adds 487 Lean modules without modifying prior Lean source.
The 23 supporting evidence files match their current Lean pins, and all 53
published named axiom reports are standard-only.

The review identified the uniform/effective composition gap and numerical-code
gap addressed above. It also distinguishes the installed tuple's all-type-code
calibration from accepted-address calibration, and records a left/right
direction typo in the frozen round-4 refitted-scalar source map. The exact old
Lean equivalence is correctly oriented; its frozen historical map is preserved.

The norm and accessibility interfaces all use the empty logical assumption
list. Their numeric source/context parameter is not a logical assumption
context. The finite-chain realization additions do not supply a general typed
lambda fundamental lemma. The abstract toy tower model does not instantiate the
paper's intended collapse.

## Native validation and preservation

[ACCEPTANCE.json](root/ACCEPTANCE.json) records every new exact endpoint, source
pin, original compilation receipt and allowed axiom set. The successful focused
gates cover a union of **3,680 local modules**. They use the unchanged serialized
wrapper and fixed profile: 2,048 MiB heap, 1,536 MiB RSS, 2,048 MiB free-memory
floor, 90 CPU seconds and 180 wall seconds per module, with one worker. The
pinned upstream cache was restored as setup; no dependency was rebuilt or pin
changed.

| Successful gate | Receipt | Result |
| --- | --- | --- |
| 01 | `1795406363595178414-12` | Uniform/effective main and frozen tower-code declarations; 2,214-module closure. |
| 04 | `1795407134226655233-11` | All nine type-boundary endpoints after the table-match rewrite repair. |
| 06 | `1795407211156632997-11` | All five coding endpoints and the coded main integration. |

All 16 accepted exact endpoints depend only on `propext`, `Classical.choice`
and `Quot.sound` (some use a subset). The original compiler rejected three
candidate module attempts: one type-table rewrite failure, one attempt with coding
calibration/syntax errors, and one with a remaining public-import error. Every failed
proof version is retained in its lane, and its raw diagnostic receipt and log
are preserved. No failed candidate is an acceptance source.

[portable-native-evidence.zip](root/portable-native-evidence.zip) contains the
full named receipts, focused proof/diagnostic logs and invocation logs. This
continuation uses the gate's source/cache checks and a focused statement/scope
comparison; it does not claim a duplicate historical artifact replay or a
full-repository build.

The 15 frozen input pins and eight baseline configuration/register pins still
match. Pre-existing Lean source, manuscript, accepted evidence, toolchain,
dependency manifest, checker, project instructions and README remain unchanged.
The shared status page is updated to link this checkpoint.

## Remaining frontier

The seven numbered statements remain pending:

- `lem:arithmetic-accessibility`: the internal arithmetic accessibility proof.
- `thm:upper`: the internal supplier and ID₁ norm theorem remain uninstantiated.
- `lem:realization`: the general fundamental-lemma wording still exceeds the
  checked abstraction and finite-chain rules; the proposed wording change is
  not applied.
- `thm:iteration`: the previous positive source comparison remains valid;
  numbered promotion remains a separate decision.
- `lem:tower-cofinality`, `thm:height` and `thm:main`: the intended ordinal
  calibration/collapse/BH suppliers remain uninstantiated.

The combined conditional main interface retains exactly `NormTheorem BH`,
`UniformAccessibility`, `Calibration D`, `TowerHypotheses D` and
`BHIdentification D BH`. The actual code theorem does not depend on them.
Future application work must preserve the actual all-type checker and obtain
the necessary internal guard laws; narrowing that slot to a finite refitted
checker cannot produce an accepted installed tuple.

All three author lanes stopped after their final ledger entries. Every owned
native process is reaped; the queue is empty and the local run policy is paused.
[STOPPED.json](root/STOPPED.json) records the closeout. No automatic successor
round or external-provider session is running.
