# K1 and the variable node — finding (root lane, 27 November 2026)

Question left open in `fableB/EXPLICIT-COVER-SCOPE.md`: do the visible wrappers of the installed cover
decide *variable* nodes themselves, or hand them to the opaque leaf programs?

**Answer: they hand them to the opaque leaves.** Files under `LogicLineages/PersistentMarking/`.

- `NumberedWindowInternalLiteralNormalizedAuxSyntaxProof.lean:25`
  `unitAuxSyntax V TV := normalize (auxSyntax V TV)`.
- `NumberedWindowInternalCoverAuxSyntaxTargets.lean:35–38`
  `auxSyntaxUpdate V T := branch certain (unaryAfter V currentKey) (auxAccept T)`,
  `auxSyntax V T := selectedMeasure (auxSyntaxUpdate V T)`. Its comment: "Use the original tag-six
  recursive row only for the physical four-field header and earlier child addresses; on other rows, the
  exact previous V program still evaluates the same key."
- `NumberedWindowInternalAuxMeasureStepTargets.lean:30–33`
  `certain := conjunction shapeCheck (conjunction (earlierAt 2) (earlierAt 3))`,
  `measureUpdate base P := branch certain (unaryAfter base currentKey) (…)` — the measure has the same shape.

So the wrappers intercept only the tag-six auxiliary rows. At a variable payload both the syntax bit and
the measure are values of `V` and `baseM` at an open term, and those are Primrec-realization witnesses
with numeric calibrations only. **K1 (`FreshAddressCarrier`) is therefore not derivable for the installed
programs as they stand.** K2 is unaffected (its seed is an auxiliary node).

## Smallest repair that would make K1 derivable

Not a full explicit syntax checker. A *front test*: programs

`V⁺ := branch isVariableNode variableCheck V`, and the same for the measure leaf and the two window leaves,

where `isVariableNode` and `variableCheck` are explicit programs (tag test, arity, type-code test through
the already visible type program). What it needs:

1. the numeric fact that on variable nodes `(syntaxBits raw).1` (and the measure, and the window test)
   equals what `variableCheck` computes — a statement about the *functions*, no program opacity involved;
2. from it and `TermSyntaxCalibrated V`: `TermSyntaxCalibrated V⁺` (all-input calibration is preserved,
   which is what every downstream theorem asks of `V`);
3. the packet and window selections re-instantiated at `V⁺` instead of the existential `V`. The consumers
   are stated for arbitrary calibrated programs, so this is selection restatement of the kind
   `exact_LambdaWindowWithLeast` already did, not new arithmetic;
4. the open-term law: at a term of variable-node shape, `V⁺`'s graph is `variableCheck`'s graph — visible
   code, decided by the shape.

Then K1 = `SeedMemberLeast` + (4) for syntax, measure and window + "the generator lists a variable node".
Size guess: comparable to Fable B's three reinstallation modules (`retypeWindow`, `reinstallFreshScalar`,
`reinstallOptionApplication`) plus the numeric fact in (1).

Not done in this round. Whether to install front tests or write explicit leaf programs is a design choice
for whoever continues the accessibility line; the front test is the smaller of the two.
