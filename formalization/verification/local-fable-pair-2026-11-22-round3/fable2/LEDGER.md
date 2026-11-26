# Fable-2 ledger — local round 3 (2026-11-22)

## G04 — type guards

### Plan

Discharge the two retained type-guard conjunctions of #1438/#1440/#1442 at `tv := TV`:
`unary TV (suc z) dom ⊓ unary TV (suc z) cod` and
`unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod`.

What was read (and only this): the three `…Targets.lean` of #1438/#1440/#1442, the #1438 proof,
`NumberedWindowInternalCoverCombinedMeasuredInstall{Definitions,Targets,Proof}.lean`, review findings 1
and 2 of `github-round2-review-2026-11-22/P16-APPLICATION-REVIEW.md`, and greps for definitions.

Diagnosis before any target was written:

1. `exact_InstalledCarrierCoordinates` returns, from `addressReport q ctx ty k` and
   `unary Q.scalar (suc z) q`: `unary cv (suc z) ctx ⊓ (unary tv (suc z) ty ⊓ (windowAt Q.window ctx ty k ⊓
   leastGraph … ctx ty k k))`. At `tv := TV` the two operands therefore supply
   `unary TV (suc z) (rawCons dom cod)` (from `qf`) and `unary TV (suc z) dom` (from `qa`). So the
   first component of the syntax guard is free; nothing else of the two conjunctions is.
2. `TV` and `T` are universally quantified `Program 1` parameters of `install` with NO calibration
   hypothesis in any of the three statements. `refitGuard s T = conjunction T (grammarTypeAt s)`
   (`NumberedWindowInternalSettingsGrammarGuardDefinitions.lean:30`), i.e. `T` plus physical membership
   in the finite list `s.types`.
3. Grep for an accepted arrow-inversion law (`ArrowInversion`, `TypeInversion`, `arrowInversion`,
   `typeGood`, `ArrowClosed`, and any target whose conclusion is `unary (refitGuard s T) (suc z) _`) in
   `LogicLineages/PersistentMarking/*Targets.lean`: no match. The only calibrations of type programs
   found (`TypeGuardCalibrated s T`, `ActualTypeGuard tv`) are numeric evaluation statements, not
   derivability laws of the internal calculus, and none is a hypothesis of the application statements.
4. Hence branch three of the task: arrow inversion is not available for arbitrary `TV`/`T` (a `TV`
   accepting the single code `rawCons a b` and nothing else is a legitimate `Program 1`), so the guards
   are derived under a NAMED calibration premise and the guard-free statements are proved under exactly
   that premise.

Premise chosen: `TypeGuardArrowCalibration body s TV T` — for all `α Γ dom cod`, from derivations of
`unary TV (suc z) (rawCons dom cod)` and `unary TV (suc z) dom` a derivation of
`unary TV (suc z) cod ⊓ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)`.
Hypotheses = exactly what scalar acceptance supplies; conclusion = exactly what is missing. Two
component laws (`ArrowCodomainInversion body TV`, `SyntaxGuardRefits body s TV T`) are stated and shown
sufficient, so the premise has a readable decomposition.

Not attempted (budget): whether `windowAt Q.window ctx ty k` already entails the refit guard at `ty`
(the base window is `numberedTypeWindow … T`, which may check `T`); if it does, the refit half at `dom`
would be free and the premise could shrink to codomain inversion of `TV` and of `refitGuard s T`.

### Targets + sha256 (recorded before the proof module was drafted)

`LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets.lean`
sha256 `59d05ab1d9b4bd5d972fb66199122a27e20447cba68a9af4bb19031d1940005d`

Definitions: `ArrowCodomainInversion`, `SyntaxGuardRefits`, `TypeGuardArrowCalibration`.
Statements: `ExactTypeGuardArrowCalibrationFromComponents`, `ExactInstalledApplicationTypeGuards`,
`ExactInstalledGuardFreeApplicationOutputAddress`, `ExactInstalledGuardFreeApplicationFrontendAcceptance`,
`ExactInstalledGuardFreeApplicationOutputFunctionalityContinuation`.

### Receipts

- `1795402283407171155-3276597` (`build-reports/1795402283407171155-3276597.json`, sha256
  `54f38d0db2b2ea0c9198827838f394b8e6bf2089a6eb18c3e4d413da4851cee8`) — `gate.sh mathlib` on
  `…GuardFreeTargets` and `…GuardFreeProof`: COMPILE_PASS for both. Five `#print axioms` lines, each
  `[propext, Classical.choice, Quot.sound]`.
- Proof module sha256 `638cbda693b86d63cf92d63c387c204467be91c4c0f195e4cb2ba750af245ccb`; targets
  sha256 unchanged from the frozen value above.

### Failures

None. One gate run, passed first time. (A plain multi-file read command was refused by the
permission mode early on; files were read with the read tool instead — no effect on the work.)

### State and next

STOPPED AT FIRST GATED STATEMENT. Result is conditional: the guards are discharged under the named
premise `TypeGuardArrowCalibration body s TV T`, not unconditionally. Evidence in
`TYPE-GUARDS-EVIDENCE.json`, claims and non-claims in `TYPE-GUARDS-SOURCE-MAP.md`.

Next, in order:
1. Read `numberedTypeWindow` / `headFittedWindow` to see whether `windowAt Q.window ctx ty k` entails
   `unary (refitGuard s T) (suc z) ty`. If yes, the refit guard at `dom` and at `rawCons dom cod` comes
   free from the operands' windows and the premise shrinks to codomain inversion of `TV` and of
   `refitGuard s T`.
2. Prove `ArrowCodomainInversion` for the actual source type program (the one calibrated by
   `ActualTypeGuard` / `TypeGuardCalibrated`), which needs an internal inversion of that program and
   closure of `s.types` under arrow components (`GrammarTypeInclusion s` is the place to look).

## G05 — calibration of the type guards

### Plan

Task: (1) does `windowAt Q.window ctx ty k` entail the refit guard at `ty`; (2) `ArrowCodomainInversion`
for the actual calibrated type program at a `Settings` with closed type list; (3) the #1453 statements
with no premise beyond that closure.

What was read: this ledger's G04 section, `TYPE-GUARDS-SOURCE-MAP.md`, the two `…GuardFree…` modules,
`NumberedWindowAdmissionAlgorithm.lean` (48 lines), `NumberedWindowInternalAuxWindowStepPrograms.lean`
lines 20–65, the three general-`tv` application targets of #1438/#1440/#1442, and greps for definitions.

Diagnosis before any target was written:

1. **The window does not test the guard at an operand's own type.** `Q.window =
   thinMatchingWindow P.cover s P.W P.V` = `conjunction (conjunction P.W (V∘proj 2)) (conjunction
   thinContextPresent (thinOwnSeed …))`, and `P.W` bottoms out in `strictAuxWindow base (refitGuard s T)
   = intrinsicQuery (strictAuxIntrinsic base (refitGuard s T))`. `intrinsicQuery F` is the equality test
   `F(ctx, k) = succ ty`. The guard program occurs in exactly one place, `admittedChildren` inside
   `strictAuxPositive` (`NumberedWindowInternalStrictAuxWindowTargets.lean:26`,
   `…AuxWindowStepTargets.lean:31`): at a key of auxiliary shape it is applied to the key's fields 0 and
   1 (`dom`, `cod`). At every other key the row is the base callback's value. So for an open `k` the
   formula `windowAt Q.window ctx ty k` contains no occurrence of the guard at `ty`; an entailment would
   need an internal case analysis on the shape of `k` plus a separate "types of windowed terms are
   guarded" lemma per shape. Grep found the forward rule only (`ExactOpenAuxWindow`: guards ⟹ window)
   and `ExactOpenCoverNumberedTypeWindow` (numbered key ⟹ grammar membership of the stored annotation,
   not of `T`, and not of the window's own `ty` in general). Numerically the same picture:
   `NumberedWindowAdmissionAlgorithm.termParts` checks `w.1.contains` on the own type for tags 0, 1, 3,
   on the arrow and the domain for tag 2, on field 1 for tag 5, on fields 1 and 0 for tag 6, and on
   **no type at all** for tag 4.
   Item 1 as posed is therefore answered NO; nothing is gated for it.
2. **The actual type programs carry numeric calibration only.** `exact_WindowPrimitiveLeaves`
   (`…AuxWindowStepPrograms.lean:52`) obtains `T` from `Proof.unaryCorrespondence` applied to
   `Primrec (typeGuard s ·)`; `ConcreteAddressPositive` and `GuardedAt` give `tv`/`T` under `∃` with
   `ActualTypeGuard tv : ∀ n, evaluate tv [n] = (typeBit n).toNat` and `TypeGuardCalibrated s T : ∀ ty,
   run T ty = (typeGuard s ty).toNat`, `typeGuard s ty = typeBit ty && s.window.1.contains ty`. These are
   existentially chosen programs with an evaluation equation and no known AST; the repository's stated
   rule (`InternalAcceptanceTargets.lean:26`) is "Natural evaluation is calibration only, never reflected
   into Derivation". No object-calculus derivation for open `dom`, `cod` follows. Item 2 as posed is
   answered: only the numeric calibration exists.
3. **Closure is not a field of `Settings`.** `structure Settings` is `window : List Nat × List Nat`,
   `types : List Nat`, `equivalentHeads`. The repository's closure predicate is `ChildClosed W`
   (`…FreshProbeDispatchWindowTargets.lean:19`: `arrow σ τ ∈ W → τ ∈ W`, codomain only) on a separate
   `W : List ProbeTy`, tied to `s` by `TypeSupport s W` inside `ValidWindow s W`, whose docstring says
   "Numerical interface only … not used as a rule of the object theory". `GrammarTypeInclusion s` is
   `s.window.1 ⊆ s.types`, not a closure. No `SubtypeClosed`-style predicate on `s.types` exists.
4. **The #1453 premise is false in the standard model for the actual calibrations.** In #1453 the
   same `TV` fills the scalar slot, whose calibration is `ActualTypeGuard` (the syntax slot asks
   `TypeSyntaxCalibrated`, whose definition I did not open). With `TV`
   calibrated to `typeBit` (all valid type codes, infinitely many) and `refitGuard s T` to `typeGuard s`
   plus membership in `s.types` (finite), `SyntaxGuardRefits body s TV T` reads "every valid type code is
   in the finite window list", and `TypeGuardArrowCalibration` fails the same way at any valid `dom`
   outside the window. This is an argument (it also needs soundness of the calculus), not a gated
   theorem. Consequence: the route "`TV` ⟹ refit guard" cannot be the calibration of the actual tuple.

What the accepted material does support (and what is attempted here): the scalar's own type-checker
slot `tv` of `install` is a free parameter in the general statements of #1438/#1440/#1442. Installing
`tv := conjunction TV (refitGuard s T)` makes scalar acceptance of the two operands supply BOTH type
programs at `rawCons dom cod` and at `dom` (`exact_InstalledCarrierCoordinates` + `conjunctionRecover`).
What remains is then exactly codomain inversion of `TV` and of `refitGuard s T` — the shrink item 1
asked for, reached through the scalar slot instead of the window. `SyntaxGuardRefits` disappears. The
refit inversion further splits (via `exact_OpenSettingsRefitGuardReports`) into inversion of `T` and
inversion of literal membership in `s.types`.

### Targets + sha256 (recorded before the proof module was drafted)

`LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets.lean`
sha256 `12593c684f85288ae3302bd34268a9b07e68c918a6a4828e1eee004031ecf932`

Definitions: `refittedScalarType s TV T := conjunction TV (refitGuard s T)`, `GrammarCodomainInversion
body s` (internal rule: membership of `rawCons dom cod` in the literal list `s.types` ⟹ membership of
`cod`). `ArrowCodomainInversion` is reused from the G04 targets.
Statements: `ExactRefitGuardCodomainInversionFromComponents`,
`ExactRefittedInstalledApplicationTypeGuards`, `ExactRefittedInstalledApplicationOutputAddress`,
`ExactRefittedInstalledApplicationFrontendAcceptance`,
`ExactRefittedInstalledApplicationOutputFunctionalityContinuation`.

### Receipts

- `1795402855547066197-3279443` (`build-reports/1795402855547066197-3279443.json`, sha256
  `fbaf544591d75df7ae9da7fc365df83410b3ccd5e55aa1e11c8d01b077b348c5`) — `gate.sh mathlib` on
  `…TypeCalibrationTargets` and `…TypeCalibrationProof`: COMPILE_PASS for both. Five `#print axioms`
  lines, each `[propext, Classical.choice, Quot.sound]`.
- Proof module sha256 `d0073128acd68b38e5efb88c177a478edabc895a1c0c6ae39de85f45bbe5cecc`; targets
  sha256 unchanged from the frozen value above.

### Failures

No failed gate (one run, passed first time). Two shell commands were refused by the permission mode
(a command substitution, and a heredoc append to this ledger); the same content was written with the
file tools instead — no effect on the work.

Task items not achieved, stated as failures of the brief rather than of the compiler:
- Item 1 (window ⟹ refit guard at its type): answered NO by reading the definitions; not gated.
- Item 2 (`ArrowCodomainInversion` for the actual type program): not provable from accepted material;
  only numeric calibration exists and `Settings` carries no closure.
- Item 3: not reached.

### State and next

STOPPED AT FIRST GATED STATEMENT. Gated: for the installation with scalar type checker
`conjunction TV (refitGuard s T)`, the three application statements with no type-guard hypothesis,
under `ArrowCodomainInversion body TV` and `ArrowCodomainInversion body (refitGuard s T)`; plus the
split of the latter into `T` and literal `s.types` membership. Evidence in
`TYPE-CALIBRATION-EVIDENCE.json`, claims and non-claims in `TYPE-CALIBRATION-SOURCE-MAP.md`.

This result is about a different installed tuple than #1453 and its two premises are open internal
statements. It should not be reported as "type guards discharged".

Next, in order:
1. Decide whether the refitted scalar is acceptable at all: check what downstream of
   `ActualTypeGuard tv` (`AddressPositiveComposition`, `ConcreteAddressPositive`, `GuardedAt`) breaks
   when `tv` computes `typeGuard s` instead of `typeBit`. If `TypeSupport`-style facts make the two
   agree on accepted addresses, the numeric chain can be re-stated; if not, this route is dead and the
   refit guard at `dom` must instead come from an internal "windowed terms have guarded types" lemma
   by shape of `k`.
2. `GrammarCodomainInversion body s` from numeric closure of `s.types` under arrow codomains: look for
   an elimination rule for `memberGraph` at a numeral list (only `ExactAllInputScratchMembership` and
   `ExactOpenScratchMinimumOccurs` were seen in `…SparseScratchMembershipTargets`). This is the one
   premise that is plausibly a finite internal case analysis.
3. `ArrowCodomainInversion` for `TV` and `T` needs named programs, not existential witnesses: replace
   `Proof.unaryCorrespondence` witnesses by an explicit `typeBit` program with an internal unfolding
   rule at `suc (pairTerm a b)`. That is new construction work, not a calibration lookup.
