# Numeric circuit encoder checked

The exact existing `CircuitLinear.Targets.NumericCircuitEncoder` is proved.
All six supporting and final aliases passed the standard-axiom audit in
`exact-gate/1793881958617312022-2.json`; definitions and exact targets passed
preflight before any candidate proof authoring. Frozen source hashes are
unchanged. `VERIFIED.json` pins all five final source files.

## Checked declarations

Namespace:
`LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitNumeric.StatementChecks`

1. `gate_code_calibration`: fixed-width natural gate records equal literal
   `gateRows` traversal with the actual `zipIdx start` indices.
2. `system_code_calibration`: raw numeric front end is exactly equal to
   `encodeCircuitSystem` on every canonical circuit code.
3. `system_code_primitive`: the concrete system builder is primitive recursive.
4. `encoder_primitive`: the concrete Option Nat encoder is primitive recursive.
5. `encoder_calibration`: its output is the actual standard Encodable system
   code, with no replacement integer codec.
6. `numeric_circuit_encoder`: the unchanged source existential target.

All actual axiom closures are subsets of `propext`, `Classical.choice` and
`Quot.sound`. No semantic source edits, new axioms, admissions, native decision
shortcuts or resource-limit increases were used. One harmless unreachable
`omega` linter warning remains in the checked length proof. The failed first
proof attempt is retained under `attempt1/`.

## Scope

The encoder is total and returns `some` on arbitrary lists. Only its behavior
on actual `encodeCircuit c` inputs is specified, precisely as required by the
source target. This is not malformed-input rejection or a complete H10 adapter.
Full circuit satisfiability, original polynomial-code rejection, nonnegative-to-
positive shifting and downstream hardness remain separately tracked obligations.

Each compiler run used one explicit parent grant and the bounded serialized
checker. The final slot was released after success; no native job is running.
