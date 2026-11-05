# Canonical numeric circuit encoder

This component targets the existing
`CircuitLinear.Targets.NumericCircuitEncoder`, without changing its type or any
literal circuit-to-system source definition.

## Input and output correspondence

- Input is the existing `CircuitReduction.encodeCircuit`: the three natural
  header fields are input count, left output and right output. Its suffix has
  exactly three natural cells per gate, with tags 0 (constant), 1 (addition) and
  2 (multiplication).
- `gateRecordRows` dispatches directly to the existing `CircuitLinear.gateRows`.
  No row, scalar index, polynomial-witness index, shared input, gate output or
  reserved auxiliary slot is independently redefined.
- `gateCodeRows` walks the actual fixed-width suffix by primitive-recursive
  range, division, natural arithmetic, defaulted list lookup and flatMap.
  The calibration is generalized over the starting gate index and compared
  with the actual `List.zipIdx start` traversal.
- `systemFromCode` retains exactly the literal input, gate, output-equality and
  constant-enforcement blocks in their original order. Its exact comparison
  is equality with `encodeCircuitSystem`, not equality only after semantic
  interpretation.
- `encode` applies the global `Encodable.encode` for the actual `SystemCode`.
  Signed coefficients use the standard Int instance. The primitive recursive
  operations on Int are supplied by checked `IntegerAlgorithmsProof`; no
  alternative integer encoding or private circuit instance is introduced.

## Scope limits

The frozen target requires calibration on canonical `encodeCircuit c` inputs,
including circuits that are not semantically well formed. The concrete encoder
is total and returns `some` off-domain as well. This is not a validity checker,
malformed-code rejection theorem or characterization of the full input-code
language. The eventual H10 adapter must separately reject malformed original
polynomial codes and apply the nonnegative-to-positive shift.

Full circuit polynomial satisfiability, the total H10 reduction and downstream
undecidability are separate obligations. This component does not claim them.

## Verification order

Definitions and six exact target propositions were frozen before proof
candidate authoring. Target-only preflight passed in receipt
`preflight/1793881616319093650-2.json`. Candidate proof checks are requested
through the parent coordinator's sole serialized compiler slot.
