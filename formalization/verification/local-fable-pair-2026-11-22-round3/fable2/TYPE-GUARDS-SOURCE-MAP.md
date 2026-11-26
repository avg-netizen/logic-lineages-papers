# G04 — type guards: source map

Modules (both new, in `LogicLineages/PersistentMarking/`):
`NumberedWindowInternalCoverMeasuredApplicationGuardFreeTargets.lean` and
`NumberedWindowInternalCoverMeasuredApplicationGuardFreeProof.lean`.
Passing receipt `1795402283407171155-3276597`. Hashes and `#print axioms` lines are in
`TYPE-GUARDS-EVIDENCE.json`.

## Outcome in one sentence

The two type-guard conjunctions are **not** dischargeable unconditionally — `TV` and `T` are arbitrary
programs — so they are replaced by one named calibration premise on `TV`/`T`,
`TypeGuardArrowCalibration body s TV T`, and the three `tv := TV` application statements are proved
with that premise in place of both guard hypotheses.

## Claimed

Throughout, `Q := install s V TV M M0 B T base cv TV root other` (scalar type checker is `TV`).

1. `exact_InstalledApplicationTypeGuards : ExactInstalledApplicationTypeGuards`.
   Given `TypeGuardArrowCalibration body s TV T`, `addressReport qf ctx (rawCons dom cod) fn`,
   `addressReport qa ctx dom arg`, `unary Q.scalar (suc z) qf` and `unary Q.scalar (suc z) qa` (all
   derivable from `Γ`), both `unary TV (suc z) dom ⊓ unary TV (suc z) cod` and
   `unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod` are derivable from `Γ`.
   Proof: `exact_InstalledCarrierCoordinates` at `tv := TV` gives `unary TV (suc z) (rawCons dom cod)`
   from `qf` and `unary TV (suc z) dom` from `qa`; the premise gives the rest.
2. `exact_InstalledGuardFreeApplicationOutputAddress`,
   `exact_InstalledGuardFreeApplicationFrontendAcceptance`,
   `exact_InstalledGuardFreeApplicationOutputFunctionalityContinuation`.
   The `…SyntaxGuarded…` statements of #1438, #1440 and #1442 with the two guard hypotheses removed and
   `TypeGuardArrowCalibration body s TV T` added; continuation and conclusions are textually unchanged
   (measured least `m`, report and scalar acceptance of `addressTerm ctx cod m`, unit graph of
   `Q.application` on `(qf, qa, addressTerm ctx cod m)`, and for every `y` the implication from
   application acceptance of `(qf, qa, y)` to `y = addressTerm ctx cod m`). Each is item 1 followed by
   the existing gated theorem; no existing proof was re-done.
3. `exact_TypeGuardArrowCalibrationFromComponents`.
   `ArrowCodomainInversion body TV` (rule: `TV` accepts `rawCons dom cod` ⟹ `TV` accepts `cod`) together
   with `SyntaxGuardRefits body s TV T` (rule: `TV` accepts `ty` ⟹ `refitGuard s T` accepts `ty`) imply
   `TypeGuardArrowCalibration body s TV T`. Unconditional.

## Assumed (explicit)

- `TypeGuardArrowCalibration body s TV T`: for all `α Γ dom cod`, derivations of
  `unary TV (suc z) (rawCons dom cod)` and `unary TV (suc z) dom` from `Γ` yield a derivation of
  `unary TV (suc z) cod ⊓ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)`.
  Its hypotheses are exactly the type facts scalar acceptance supplies; its conclusion is exactly the
  part of the two conjunctions those facts do not contain. It is a hypothesis about the two type
  programs only — it mentions no address, window, least call, scalar or application program, and it is
  not the conclusion of any of the application statements.
- It is stated as a rule over derivations at one `body`, quantified over every context `Γ`, not as one
  derivable implication formula. The proofs use it only at the statement's own `α`, `Γ`, `dom`, `cod`.
- The two operand reports at one shared `ctx` and the two scalar acceptances, as before.

## Not claimed

- **No unconditional removal of the guards.** No arrow-inversion law for `TV` or for `refitGuard s T`
  exists among the accepted targets (greps recorded in the ledger), and none is provable for arbitrary
  `Program 1` parameters: a `TV` accepting one arrow code and nothing else is a legitimate program. The
  statement "the guards follow from scalar acceptance alone" is therefore not proved, and I did not
  prove a formal counterexample either — the non-derivability is an argument, not a gated theorem.
- **No instance of the premise.** No concrete `TV`/`T` is shown to satisfy
  `TypeGuardArrowCalibration`, `ArrowCodomainInversion` or `SyntaxGuardRefits`. In particular the
  premise is not derived from the numeric calibrations `TypeGuardCalibrated s T` / `ActualTypeGuard tv`;
  that needs an internal (derivable) inversion for the actual type programs plus closure of the finite
  list `s.types` under arrow components, since `refitGuard s T` includes membership in `s.types`.
- **Minimality is not proved.** "Weakest" is by construction (hypotheses = what is supplied, conclusion
  = what is missing, along the route through `exact_InstalledCarrierCoordinates`). Not checked: whether
  `windowAt Q.window ctx ty k` already entails the refit guard at `ty`, which would make the `dom` half
  of the refit conjunct free and shrink the premise.
- The arbitrary-`tv` general statements of #1438/#1440/#1442 are unchanged and still carry
  `unary tv (suc z) cod`. Nothing here relates an arbitrary scalar type checker to `TV`.
- All remaining boundaries of the round-2 review stand: output witness under the object continuation
  only, functionality as a schema over terms, one shared context, no numbered Paper 16 statement closed.
