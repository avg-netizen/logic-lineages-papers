# Paper 16: reusable exact own-scratch continuations, instantiated at refined V

Frozen draft, native gate pending. Generic continuation roots
`exact_OpenCoverLocalLambdaOwnContinuation` and
`exact_OpenCoverLocalAuxOwnContinuation`; refined literal roots
`exact_OpenCoverRefinedLambdaOwnScratch` and
`exact_OpenCoverRefinedAuxOwnScratch`.

The new continuations accept the actual validity program V and selected
measure updater R as literal program parameters. The parent record keeps its
actual V, selected R measurement, and the same actual
`scratchVertices (selectedCover V (selectedMeasure R))` report together.
The child requires actual local typed W, actual valid V and its exact
object-local scratch IH on the very same selected cover. The continuation
observes actual grammar at the pair of the child's same selected R measure.
It reuses the previously checked lambda placement or auxiliary #975 actual
bounds assembly. There is no assumed program equality or transfer of a
scratch graph across different V callbacks. K membership remains explicit.

The refined lambda adapter uses the actual V⋄ parent/child and shared M⋆
parent/child pair proof. Its exact body W and body IH remain explicit.
The refined auxiliary adapter uses actual V⋄ propagation, the strict
actual typed parent window and actual same-context function/argument
windows, and the two actual shared M⋆ child codes and bound report. Both
local IHs remain explicit at those types. Bounds from the same shared M⋆
row are not recomputed on a former measure program.

Both conclusions are scoped to the original literal lambda or auxiliary
key and the supplied actual refined scratch. No all-constructor or whole
own-cover induction, arbitrary raw parent wrapper, old V/V⋆ reflection, or
protected/fresh-port W closure is asserted.

## Frozen sources
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLocalOwnContinuationTargets.lean`: `f7aeb0d75094244f35d70364bd5c9887c55c203646532e0ec939cf397efec085`, 1169 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLocalOwnReportRenameProof.lean`: `819c14c9c6185697584f1d83cf49ab5c2ee40638209ba123efde1463c2c096ff`, 1210 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLocalLambdaOwnContinuationProof.lean`: `efa26c1368c69ba5ead28db3796e7c5221e97301bd33ee0bf72401987fddf533`, 1494 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLocalAuxOwnContinuationProof.lean`: `534ddb0bb5e7bfa1add8cc22bce90411ddaf148ea750db729d3f62e5cf37c644`, 1498 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverRefinedLambdaOwnScratchProof.lean`: `7c3e357b17ea7c4013e6c4ff1dd75f5a82f80c1da3f71b6fc3115b9b5be1e61e`, 1523 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverRefinedAuxOwnScratchProof.lean`: `c110d289f2a5b3093c12cfe22b7cd1460cad991f16ee3f33aaf3b576ea087368`, 1534 local modules.
No explicit Hydra or Linarith in these static local import closures.

## Principal exact origin pins
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverRefinedSharedSyntaxTargets.lean`: `68aa7f0e1cff597475634bc56fa34f11c0ba046a17f2dcc87fb69572def36778`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverRefinedLambdaSyntaxProof.lean`: `a2e1253095e24a941da4c23028a9a1c6765d7e0f508500885db3097c988d5521`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverRefinedAuxSyntaxProof.lean`: `9ed872e4e2ee817b64146b79cfd67fdbe2b5651b6b106e124e5a34ed7932afef`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedLambdaMeasureProof.lean`: `f1c2ea9818cb57529a919992fd5b6dab20d7f0f3fcb5876fac9f44e2ecacf5bb`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxMeasureProof.lean`: `62beb8006fdce2832c13f400ff92582958cf5a4e3b56dac234096a0f960a7730`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedOwnScratchTargets.lean`: `4ece283b7611f0815c08a6dc0fcf3997c664e2ed55487427476c0f8ff621bf60`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverChildOwnScopeProof.lean`: `64db0bc179520687ecdc028491d69354e7176bac2961dfef493072eb885f2349`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof.lean`: `9f57d49856d06a71951c17b90038aa545812bc4472394c93896895dd78eba812`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarLambdaOwnScratchProof.lean`: `3fd45e718b72e5bb5428fce0bcc70c0ac0fd65f59c589f5c4955d1f5bcd08bec`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSelectedGrammarAuxScratchMembershipProof.lean`: `662c2cf7b678c3c20eb0ec6774c589e0c00bbb913c934774502a9e068e5d93c5`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalStrictAuxWindowParentProof.lean`: `eab706f734ba54165112f3e0b93ccac58c49ab26f8b92751fa4d9d25ae269e25`.
