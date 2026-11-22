# RAW-PACKET-ALGEBRA groups 4 (reify) and 5 (assembled child) — source map (Opus B)

Both Targets compiled together and were frozen at 2026-11-22T22:16Z (receipt `1795385752127892140-3153782`):
- `LogicLineages/PermittedControl/RawPacketAlgebraReifyTargets.lean` sha256
  `1520ff85775a6723b2aaed958428655c7207eb4162c05ef9b36946a5d350a92b`
- `LogicLineages/PermittedControl/RawPacketAlgebraChildTargets.lean` sha256
  `0700af0e8508a7691918c0e81f194fa72302d8b16796b12842f4a0bb54b022ee`

## Group 4: `reify` / `reifyFamily` on `ResidualCode`

- `availabilityCode` and `lowerChartCode` are the literal codes of `availabilityRows` and `lowerChart`.
- `reifyCode` uses the accepted `OriginalPrintedRawClauseAssembly.clausesCode` (#1343).
- `reifyFamilyCode := flatMap reifyCode`.
- Statements: `ExactAvailabilityCode`, `ExactLowerChartCode`,
  `ExactReifyCode : reifyCode C top (encodeResidual out) = encodeFamily (reify C top out)`, and
  `ExactReifyFamilyCode`. All are for every residual, with no hypothesis.
- `ReifyEffectivity` is Primrec.

## Group 5: the assembled map Fable-2 asked for

- `childCode (C, top, cs) := reifyFamilyCode C top (lowerFamilyCode top C (cs.map (prependCode top)))`.
- `ExactChildCode`: `childCode (C,top,qs.map encodePacket) = encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top))))`
  for every packet list, with NO shape hypothesis.
- `ChildEffectivity`: `Primrec childCode ∧ Computable childCode`.
- The only new code on the path is `ResidualCode`/`encodeResidual` (group 3, flagged there). It is internal
  to `childCode`; input and output are the existing `preparedPacketCode` and `encodeFamily`.
