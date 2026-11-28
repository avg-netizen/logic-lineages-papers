# Source map — arrow typing targets (Fable B, 27 November 2026)

Four frozen Targets modules (prefix `LogicLineages.NativeModule.PersistentMarking.`):

| Module | sha256 | Frozen |
| --- | --- | --- |
| `Paper16AccessibilityMilestoneArrowTypingTargetsV2` | `dfd27747d4e736c0e3c310f8bc7b3d6a1a750cbea04a62325de1890070569037` | before gate 2 |
| `Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2` | `465712db58cb67def3e277bec4a39bec5a1413c88c890124e1e22fbbedfc26c0` | before gate 3 |
| `Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2` | `2891fda3ce1bba9cb808cf26ccfea9f7781383dd99ed9256fe5be4663d9067eb` | before gate 4 |
| `Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2` | `ef3a3740553bcbf52cc6e33325b39e4b09319ce5b1978b19b655316161d39865` | before gate 6 |

## What they serve

Paper 16 `lem:arithmetic-accessibility` (`16-persistent-marking-termination-ordering/sections/ordinals.tex:79`),
Lean target `Paper16AccessibilityMilestoneTargetsV2.InstalledArithmeticAccessibility`; in
`verification/paper16-remaining-targets-2026-11-25/TARGETS.md`, internal accessibility checkpoint 5
("Discharge `CarrierTypingCases` for admitted addresses. Use `CloseAllTerms` at the same context")
and the fresh/application/codomain obligations listed at the end of
`verification/local-fable-continuation-2026-11-25/2026-11-26/native-window-v2-rebase.md`.

Manuscript correspondence. The paper works in one finite subtype-closed universe in which every
admitted term has a type and, for a term `Q` of type σ→τ and a fresh variable `x:σ`, the application
`Q x` is again an admitted term of type τ (the step "computability implies I" applies `Q` to fresh
variables). The formal checker `chosenH` records exactly that: an address is typed at σ→τ when the
fresh selector answers, the application to that fresh address is accepted, and the result is typed
at τ. `CarrierTypingCases` is the internal statement that every admitted address is so typed at
one of the universe's types.

## Definitions

- `storedType τ q` — the graph of the result-field projection `rawResult` at `q` with output the
  literal code of `τ`. `storedTypeChoices W q` — finite disjunction over the window.
- `typedResultAt p τ q u` — `∃ v (accepts p q u v ∧ storedType τ v)`.
- `FreshApplicationTotal A c` — **the open obligation**: from the carrier of `q`, stored type σ→τ
  (listed in the window) and the selected fresh address `u`, derive `typedResultAt … τ q u`.
- `ApplicationResultCarrier A c` — an accepted application has a carrier result.
- `LiteralProbeReports A c` — five open report rules of the probe leaves (stored type listed, prior
  typing, fresh selection, option output, result carrier).
- `StoredTypeTyping A c` — carrier + stored type ρ ⇒ `typedAt (chosenH …) ρ`.
- `literalProbeWindow A` — `reinstallOptionApplication (reinstallFreshScalar (retypeWindow A))`.

## Statements and what is assumed

- `StoredTypingFromReports A c`, `TypingCasesFromReports A c` (for `A` over `sourceWindow K`):
  assume `LiteralProbeReports A c` and `FreshApplicationTotal A c`; conclude `StoredTypeTyping A c`,
  respectively the milestone's `CarrierTypingCases A c`.
- `StackedLiteralProbeReports`: assume `A.scalar = finiteScalar (addressScalar … forming A.least)
  (finiteCodes (sourceWindow K))`, `A.application = applicationCore A.least`, and
  `ApplicationResultCarrier A c`; conclude `LiteralProbeReports (literalProbeWindow A) c`.
- `WindowReductionFromJoinedFacts`: assume the same shape and core, `ApplicationResultCarrier A c`,
  the neutral `Arithmetic` package and `ForwardRule` on `A.presentation` at `A`'s application
  guard; conclude on `B = literalProbeWindow A`:
  `(FreshApplicationTotal B c → CarrierTypingCases B c) ∧
   (CarrierTypingCases B c → TypedCarrierComputability B c → AllTerms B c)`.
- `InstalledAccessibilityReduction`: for every closed `K`, one window over `sourceWindow K` with
  both implications for all `c`. Its hypotheses are those the joined lambda window
  (`exact_InstalledLambdaWindowWithScalarAtOriginalWindow`) provides.

- `GroundUniverseReduction`: assume `K` closed and every type of `K` ground; conclude one window with
  `CarrierTypingCases A c ∧ (TypedCarrierComputability A c → AllTerms A c)` for all `c`. The window lists
  no arrow type, so `FreshApplicationTotal` has no instance.

## Not claimed

- `FreshApplicationTotal` for any window. No theorem here derives an application acceptance that
  is not handed in.
- `TypedCarrierComputability`, `ApplicationArithmetic` (in particular backward matching),
  `InstalledArithmeticAccessibility`, or any numbered statement of Paper 16.
- That the selected window of `InstalledAccessibilityReduction` is the one a later proof of
  `TypedCarrierComputability` will use; the reduction is per window.
