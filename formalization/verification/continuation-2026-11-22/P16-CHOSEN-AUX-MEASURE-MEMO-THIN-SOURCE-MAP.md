# Paper 16: narrow exact-gate route for the original chosen auxiliary memo row

Source only; proof/axiom gates pending. The original row target already
passed target-only gate 1795343029541984399-8 and is unchanged. The
broader first proof root is unchanged and is not presented as checked.

The old `ExchangeRowMemo` base/step/table/row definitions and the
existing physical `scratchBase/scratchStep/scratchTable/scratchRow`
constructors have the same literal cons, recursion and head projection
ASTs. The thin lookup uses the latter directly. Its syntax, one-step
table-tail and finite offset induction are the generic portions of
`ExchangeRowMemo/{SyntaxProof,TailProof,TableProof}`; no source-specific
exchange layers or native arithmetic are imported. The exported
`exact_OpenThinScratchMemoLookup` has the same existing exact
`ExactOpenSelectedMemoLookup` type: an actual row at key and a physical
table at key+offset give original lookup of that row at the same offset
and physical table, with both scratch parameters still zero.

The successor proof preserves the existing exact table extension and
read-head derivation; no lookup dependency is required for that step.
The thin slot reuses the previous slot derivation with only its lookup
supplier changed. `exact_OpenChosenAuxMeasureMemoRow` at the thin root
retains the entire original target/type, same literal physical tape and
actual order/shape/read reports, same selected program and same output p.
Static local counts: lookup 1,095; successor 1,085; slot 1,250; exact
row root 1,296. No explicit Hydra/Linarith or legacy ExchangeRowMemo
module remains in those closures.

| Module | SHA-256 |
| --- | --- |
| `NumberedWindowInternalScratchMemoThinLookupSyntaxProof` | `18dcf3279beef9f806f123b624433e87921b97a77ca6faf3ad2231b90b38633a` |
| `NumberedWindowInternalScratchMemoThinLookupTailProof` | `950bd272fde994d540550499ad1724e6e2c0c9314a5de41d5ef6c95f32998de9` |
| `NumberedWindowInternalScratchMemoThinLookupChecks` | `fa998fb0c91f23d5846c887d99eaec04d92248cf82821519f327cff6ae653fb3` |
| `NumberedWindowInternalScratchMemoThinSuccessorProof` | `1a8dfe73356a1915c638a9adfe38b0c8298139ff6a11c98abbcbc94948333ba7` |
| `NumberedWindowInternalAuxMeasureOpenThinSlotProof` | `b05844bf318e4e15547881cb1d75042f8f4fe4f56727df2bd8637d4facb3f1b0` |
| `NumberedWindowInternalChosenAuxMeasureMemoThinChecks` | `edd65b7c7cf7080be5c6f4cefff9846c380d8d22e4cd80bb3d03224063a43598` |
