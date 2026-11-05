# Original H10 validity checked

Five exact aliases pass, including exact arbitrary-list recognition and
primitive recursion of `validInput : List Nat → Bool`.

Namespace:
`LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.H10Validity.StatementChecks`

1. `variables_validity`: every listed index is below the original arity.
2. `terms_validity`: every occurrence in every original term satisfies that bound.
3. `input_validity`: the raw list is accepted iff the actual decoder returns
   some original code satisfying the actual `Code.WellFormed` predicate.
4. `canonical_validity`: canonical polynomial codes are accepted exactly when
   the original polynomial code is well formed.
5. `validity_primitive`: the actual Boolean validator is primitive recursive.

## Evidence

- Definitions/targets preflight: `preflight/1793882212553941866-2.json`.
- Calibration module passed in `attempt1/1793882429987632460-2.json`.
  That first candidate gate stopped later at a missing Bool motive in the
  final list-case wrapper; the failed proof and logs are retained.
- Repaired Programs and all five exact aliases passed in
  `exact-gate/1793882686907137612-2.json`.
- `VERIFIED.json` pins every final file, validates all successful module hashes
  and confirms the frozen semantic/target files remain unchanged.

Actual axiom closures are subsets of `propext`, `Classical.choice` and
`Quot.sound`. No source semantic changes, admissions, added axioms, native
shortcuts, alternative Int encoding or private Code encoding were used.
Accepted CircuitNumeric source hashes also remain unchanged.

The final serialized compiler slot was explicitly transferred to the parent
for its separately authorized H10Adapter gate. No compiler job remains here.

## Scope

This validates the original input before shifting or compilation. It checks
zero-coefficient terms too, as required by the literal source WellFormed
predicate, so invalid original indices cannot masquerade as emitted gate wires.
This supporting component alone is not the complete H10 reduction or any
undecidability/hardness conclusion.
