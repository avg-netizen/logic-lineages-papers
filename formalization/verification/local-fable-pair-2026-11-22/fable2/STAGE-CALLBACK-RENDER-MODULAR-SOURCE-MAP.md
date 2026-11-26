# Paper 17: raw rendering of the congruence packet

Key: `STAGE-CALLBACK-RENDER-MODULAR`. Targets module
`LogicLineages.PermittedControl.StageCallbackRenderModularTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`, subsection "Residues, finite strips, and one-variable projection": "converts every
current field congruence modulo m into a finite Presburger condition on its original raw input modulo
2m … All occurrences of the same x use one shared residue." This key is the code-level form of the
accepted congruence packet (#1245); it is the `modular` field of
`StageCallbackRawLevel.Rendering` (#1398).

## What is stated

- `lowerRanksCode top ts` — the accepted literal rank support `rankSupportCode`, kept below `top`.
- `modularCode top m s positive` — one bare coordinate slot per lower rank as table bytes; the
  accepted residue-row formula code `SharedRankResidueRow.formulaCode` on the layout
  `(0, top) :: namedSlots (lower ranks)`; then `polarityCode`.

Targets:

- `ExactModularCode` — for every `top`, **every modulus `m` including zero**, typed syntax and
  polarity, `modularCode top m (encodeSyntax s) positive
     = encodePacket (ActualGreatestCongruenceRoute.packet top m s positive)`.
  This is literally `Rendering.Exact.modular` for `R.modular := modularCode`.
- `ModularCodeEffectivity` — `Primrec₂ lowerRanksCode`, `Primrec` of `formulaCode` (uncurried), and
  `Primrec` of `modularCode` (uncurried).

## What is assumed

Nothing.

## What is not claimed

- Nothing outside the encoder image.
- No semantic statement about the packet (that is #1245), and nothing for modulus zero beyond the
  literal code equation: a congruence row with modulus zero is not admitted and its clause is
  removed by the proper-clause filter before any packet is used.
- The accepted `SharedRankResidueRow.CodeExact` calibrates the formula code only through
  `prepareCode`, which is `none` at modulus zero. The unconditional literal equation
  `formulaCode layout (m, c, ts.map encodeWeighted) = (formula layout (m, c, ts)).encode` and
  `Primrec` of `formulaCode` are restated here following the accepted private proofs
  (`formulaLiteral`, `formulaStepPrimitive` in `SharedRankResidueRowCodeProof`), which do not use
  positivity of the modulus. No accepted module is edited.
