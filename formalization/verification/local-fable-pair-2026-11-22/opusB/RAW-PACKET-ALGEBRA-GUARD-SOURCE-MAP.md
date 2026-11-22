# RAW-PACKET-ALGEBRA group 2 (guards + projection) — source map (Opus B)

Targets: `LogicLineages/PermittedControl/RawPacketAlgebraGuardTargets.lean`, sha256
`6eb200a5609b4e1b8c4ccab3441d9d51cb5afebb8125910d04cd03f7e280f4cc`, frozen 2026-11-22T22:06Z after compiling alone
(receipt `1795385184265797565-3151419`).

Serves Task 4 group 2: `prepend (top p)` in `StageCallbackSupplier.outputs` and the `project` inside
`ActualGreatestRouteResidual.decodeRoute`, on the existing packet code.
- `predecessorCode` / `cutoffCode` are the literal codes of `predecessorPacket top` / `cutoffPacket minimum`
  written as explicit numerals.
- `prependCode`, `boundedCode` use group 1's `appendCode`.
- `projectCode := eliminatePreparedCode ∘ boundedCode` uses the accepted #728 kernel.

Statements:
- `ExactPredecessorCode`, `ExactPrependCode`, `ExactCutoffCode`, `ExactBoundedCode`, `ExactProjectCode`.
- `GuardEffectivity`: Primrec predecessorCode / cutoffCode, Primrec₂ prependCode / boundedCode / projectCode.
- Everything is for all typed packets and all `top`, `minimum`, with no shape hypothesis. The calibration of
  `eliminatePreparedCode` in #728 is itself unconditional.

No new encoding.
