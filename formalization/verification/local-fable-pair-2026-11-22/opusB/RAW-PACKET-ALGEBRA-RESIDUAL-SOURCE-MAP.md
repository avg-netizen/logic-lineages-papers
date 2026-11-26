# RAW-PACKET-ALGEBRA group 3 (decode / keep / lowerFamily) — source map (Opus B)

Targets: `LogicLineages/PermittedControl/RawPacketAlgebraResidualTargets.lean`, sha256
`2f88a8c86fa34c3477941cea211b1d967a1b95ef33225eb19f3a01e3947b0bd2`, frozen 2026-11-22T22:10Z after compiling alone
(receipt `1795385442097803207-3152345`).

Serves Task 4 group 3: `ActualGreatestRouteResidual.lowerFamily (top p) C` in `StageCallbackSupplier.outputs`.

Raw functions:
- `decodeTermCode` / `decodeTermsCode` / `testOfCode` / `decodeRowCode` / `decodeAtomCode` / `decodeAtomsCode` /
  `decodeCode`: code of `OriginalProjectedMatrixDecode.decode`, reading atoms with the existing
  `LinearRows.Code.atoms` and `LinearRows.Code.decodeAtom`.
- `residualOf`, `decodeRouteCode := residualOf ∘ projectCode` (group 2).
- `keepCode`: the rank is component 2 of every operand code.
- `lowerFamilyCode`.

**NEW ENCODING (design decision, flagged):** `ResidualCode := List LowerOperandCode × Nat × List RawRow` and
`encodeResidual r := (r.ops.map LowerOperand.code, r.formula.encode, r.atoms.map encodeRow)`. `Residual` had no
code anywhere. This is the minimal one: a tuple of the existing codes of its three fields, with no new
code for any field. No injectivity is needed for any equation in this group or for group 4, which takes
`ResidualCode` as input and is calibrated by equations.

Statements: `ExactDecodeCode`, `ExactDecodeRouteCode`, `ExactKeepCode`, `ExactLowerFamilyCode`. All are for
every typed operand list, formula and packet, with no shape hypothesis. `decode` is total, including
on formulas that the residual layer would reject as unshaped (they give `none` on both sides).
Effectivity: Primrec₂ decodeCode / decodeRouteCode / keepCode, and Primrec of the uncurried lowerFamilyCode.
