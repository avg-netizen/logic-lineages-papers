# STAGE-CALLBACK-GUARD-RENDER — source map (Opus B)

Targets: `LogicLineages/PermittedControl/StageCallbackGuardRenderTargets.lean` (namespace
`LogicLineages.PermittedControl.StageCallbackGuardRender`), sha256
`ad8b4423a3a13e485bf91f28687717210c49773ab3f25de518875ba1e9abe6e3`, frozen 2026-11-22T22:32Z after the module compiled
alone (receipt `1795386726818073956-3157693`).

## What it serves

Root Task 6. This is the `guard` field of `StageCallbackRawLevel.Rendering.Exact`:
`R.guard top ((labels grouped).map encodeLabel) (a.map Answer.code) = encodePacket (StageCallbackCanonicalRoutes.guard top grouped a)`,
which is literally `ExactGuardCode`. The effectivity is `Primrec (fun p : Nat × List LabelCode × List Nat => guardCode p.1 p.2.1 p.2.2)`,
the `guard` field of Opus A's `StageEmitter.RenderingEffective`.

## Program

`guardCode top ls as := compileCode top (orderedPairs ls) as`:
- `orderedPairs` is the accepted raw pair list.
- `compileCode` uses the same recursion as `ActualFiniteFullValueGuards.compile`, including the `([],⊥)` code
  on tapes of the wrong length.
- `pairCode` is the code of `ActualFullLabelPairGuards.packet`:
  - if both ranks are below `top`, the literal two-slot lower packet;
  - otherwise `topCode`, the code of `orientedPacket` at `topRequest a` with positive polarity:
    - strict order goes through the accepted `HighFieldPreparedPacket.compile`, then a bare coordinate slot
      and the order guard;
    - equal ranks go through the accepted `normalizeHighFieldCode` and `rawSameForm`.

For every answer, `topRequest` gives requested code = answer code and wanted bit = true; in the reversed
orientation the requested code is `2 - answer code`. So no polarity code is needed (`choosePolarity · true` is the identity).

## Statements

`ExactPairCode` and `ExactCompileCode` hold for every pair list and every tape. `ExactGuardCode` is the field.
`GuardCodeEffectivity` is Primrec of `pairCode`, `compileCode` and `guardCode`, uncurried.

## Assumed / not claimed

The only hypothesis used is `lo < hi` of the accepted `StableSortedHighField.BasePacketExact`. It holds in both
strict branches by the branch condition, so it is not a hypothesis of any statement. No new encoding.
