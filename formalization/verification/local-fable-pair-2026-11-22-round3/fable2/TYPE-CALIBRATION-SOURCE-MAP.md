# G05 — calibration of the type guards: source map

Modules (both new, in `LogicLineages/PersistentMarking/`):
`NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets.lean` and
`NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationProof.lean`.
Passing receipt `1795402855547066197-3279443`. Hashes and `#print axioms` lines are in
`TYPE-CALIBRATION-EVIDENCE.json`.

## Outcome in one paragraph

Neither of the two things the task hoped for is available from the accepted material: the installed
window does **not** entail the refit guard at an operand's own type, and the actual type programs have
**only numeric** calibration, so `ArrowCodomainInversion` cannot be proved for them. What is gated is
the premise shrink by a different, supported route: install the scalar with type checker
`conjunction TV (refitGuard s T)`. Then operand acceptance supplies both type programs at the arrow
and at the domain, and the three application statements hold under codomain inversion of `TV` and of
`refitGuard s T` only. This is a statement about a different installed tuple than #1453.

## Claimed

Throughout, `Q := install s V TV M M0 B T base cv (refittedScalarType s TV T) root other`, with
`refittedScalarType s TV T := conjunction TV (refitGuard s T)`.

1. `exact_RefittedInstalledApplicationTypeGuards : ExactRefittedInstalledApplicationTypeGuards`.
   Given `ArrowCodomainInversion body TV`, `ArrowCodomainInversion body (refitGuard s T)`,
   `addressReport qf ctx (rawCons dom cod) fn`, `addressReport qa ctx dom arg`,
   `unary Q.scalar (suc z) qf` and `unary Q.scalar (suc z) qa` (all derivable from `Γ`), the following
   are derivable from `Γ`: `unary TV (suc z) dom ⊓ unary TV (suc z) cod`;
   `unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod`; and
   `unary (refittedScalarType s TV T) (suc z) cod`.
   Proof: `exact_InstalledCarrierCoordinates` at `tv := refittedScalarType s TV T` for each operand,
   `conjunctionRecover` to split the scalar's type fact into its `TV` and refit halves, the two
   inversions at `rawCons dom cod`, `conjunctionAccept` to rebuild the scalar's type fact at `cod`.
2. `exact_RefittedInstalledApplicationOutputAddress`,
   `exact_RefittedInstalledApplicationFrontendAcceptance`,
   `exact_RefittedInstalledApplicationOutputFunctionalityContinuation`.
   The general-`tv` statements of #1438, #1440 and #1442 at `tv := refittedScalarType s TV T`, with all
   three type-guard hypotheses removed and the two inversion premises added. Continuation and
   conclusions are textually those of the general statements (measured least `m`, report and scalar
   acceptance of `addressTerm ctx cod m`, unit graph of `Q.application`, and for every `y` the
   implication from application acceptance of `(qf, qa, y)` to `y = addressTerm ctx cod m`). Each is
   item 1 followed by the existing gated general theorem; no existing proof was re-done.
3. `exact_RefitGuardCodomainInversionFromComponents`.
   `ArrowCodomainInversion body T` together with `GrammarCodomainInversion body s` imply
   `ArrowCodomainInversion body (refitGuard s T)`. Unconditional; uses
   `exact_OpenSettingsRefitGuardReports` in both directions.

## Assumed (explicit)

- `ArrowCodomainInversion body TV` and `ArrowCodomainInversion body (refitGuard s T)` (definition from
  the G04 targets): for all `α Γ dom cod`, a derivation of the program at `rawCons dom cod` from `Γ`
  yields a derivation of it at `cod`. Rules over derivations at one `body`, quantified over every
  context; used only at the statement's own `α`, `Γ`, `dom`, `cod`.
- For item 3 only: `GrammarCodomainInversion body s`, the same rule for
  `memberGraph (numeral (Encodable.encode s.types)) ·`.
- The two operand reports at one shared `ctx` and the two scalar acceptances, as before.
- **Status of these premises.** In the standard model each is true exactly when the corresponding
  finite datum is closed under arrow codomains (`s.window.1` for a `T` calibrated to `typeGuard s`,
  `s.types` for the grammar half; `typeBit` is closed outright). So their numeric shadows are finite,
  checkable properties of the settings. As stated — rules of the object calculus for open `dom`, `cod`
  — they are **open internal statements**: no accepted theorem turns the numeric fact into the rule.

## Not claimed

- **Item 1 of the task: the window does not entail the refit guard at its type.** In
  `Q.window = thinMatchingWindow P.cover s P.W P.V`, the only occurrence of the guard program is in
  `admittedChildren` (`strictAuxPositive`), applied to fields 0 and 1 of a key of auxiliary shape;
  `intrinsicQuery` itself is the equality `F(ctx, k) = succ ty`. The accepted open rules go the other
  way (`ExactOpenAuxWindow`: guards ⟹ window) or give grammar membership of a numbered key's stored
  annotation (`ExactOpenCoverNumberedTypeWindow`). This is a reading of the definitions, **not** a
  gated non-derivability theorem.
- **Item 2 of the task: no `ArrowCodomainInversion` for the actual type program.** The calibrations
  that exist are `ActualTypeGuard tv : ∀ n, evaluate tv (n ::ᵥ nil) = (typeBit n).toNat` and
  `TypeGuardCalibrated s T : ∀ ty, run T ty = (typeGuard s ty).toNat`, and the programs are obtained
  under `∃` from `Proof.unaryCorrespondence` on a `Primrec` proof (`exact_WindowPrimitiveLeaves`). The
  internal statement that would be needed, for a **named** program `P` rather than an existential
  witness: for every `body α Γ dom cod`, `Γ ⊢ unary P (suc z) (rawCons dom cod)` ⟹
  `Γ ⊢ unary P (suc z) cod`. For the grammar half this is a finite case analysis on the literal list
  `s.types` (needs: an elimination rule for `memberGraph` at a numeral list, injectivity of `rawCons`
  against numerals, and numeric closure of `s.types`); for `typeBit` it needs a concrete
  course-of-values program and its internal unfolding at a successor-of-pair code.
- **No closure hypothesis on `Settings` is introduced or used.** `Settings` has no closure field;
  the repository's predicate is `ChildClosed W` on a separate `W : List ProbeTy` linked by
  `TypeSupport s W` in `ValidWindow s W`, documented as "Numerical interface only … not used as a rule
  of the object theory". I did not add a numeric closure definition because no gated statement here
  could consume it.
- **Item 3 of the task is not reached.**
- **Nothing about the `tv := TV` installation of #1453.** Its premise `TypeGuardArrowCalibration`
  (through `SyntaxGuardRefits`) reads, under the actual calibrations, "every valid type code lies in
  the finite window list" and is false in the standard model. That is an argument, not a gated
  theorem; it also relies on soundness of the calculus, which I did not look up.
- **The refitted scalar is not shown to be an accepted installation.** `refittedScalarType s TV T` does
  not satisfy `ActualTypeGuard` (numerically it is `typeGuard s` plus membership in `s.types`, narrower
  than `typeBit`). Whether `ConcreteAddressPositive` / `GuardedAt` and everything downstream of
  `ActualTypeGuard tv` survive this choice was not examined. Until it is, the gated statements describe
  a well-defined installed tuple whose numeric acceptance of the paper's addresses is unverified.
- All remaining boundaries of the round-2 review stand: output witness under the object continuation
  only, functionality as a schema over terms, one shared context, no numbered Paper 16 statement closed.
