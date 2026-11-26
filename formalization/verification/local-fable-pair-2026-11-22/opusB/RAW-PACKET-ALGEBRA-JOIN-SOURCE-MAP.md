# RAW-PACKET-ALGEBRA group 1 (join) — source map (Opus B)

Targets: `LogicLineages/PermittedControl/RawPacketAlgebraJoinTargets.lean` (namespace
`LogicLineages.PermittedControl.RawPacketAlgebra`), sha256 `4c8ee91c67c2648f74cb2dc06ace5b610f859a01654122f0fa3098cef2fb04db`, frozen 2026-11-22T22:03Z after the Targets
module alone compiled (receipt `1795384978040632556-3150351`).

Serves root Task 4, group 1: the code-level join between the supplier's packets and
`StageCallbackSupplier.packets`, i.e. `(choices rows).map tuplePacket`, through the existing packet code
`encodePacket p := preparedPacketCode p.1 p.2` (#728: table bytes = `Encodable.encode (table.map LowerOperand.code)`,
formula = `NormalForm.Formula.encode`). No new encoding: `encodePacket` is a name for `preparedPacketCode`.

Raw functions: `tableOf` (decode of table bytes, `[]` on failure), `shiftNameCode`/`shiftItemCode`/`shiftRowCode`/
`shiftAtomData`/`shiftAtomCode` (positive-name shift on atom data), `shiftCode d := LinearRows.Code.mapAtoms (shiftAtomCode d)`
(existing radix-six atom map), `appendCode`, `unitCode`, `tupleCode` (foldr), `choicesCode` (same recursion as
`choices`), `joinCode`.

Statements (all for every typed input, no shape hypothesis — `shift`/`append`/`tuplePacket`/`choices` are total):
`ExactShiftCode`, `ExactAppendCode`, `ExactTupleCode`, `ExactChoicesCode`, `ExactJoinCode`
(`joinCode (rows.map (List.map encodePacket)) = ((choices rows).map tuplePacket).map encodePacket`), bundled as
`JoinCalibration`; `JoinEffectivity` = Primrec₂ shiftCode/appendCode, Primrec tupleCode/choicesCode/joinCode.

Not claimed: anything on codes outside the encoder image (undecodable table bytes are read as `[]`).
