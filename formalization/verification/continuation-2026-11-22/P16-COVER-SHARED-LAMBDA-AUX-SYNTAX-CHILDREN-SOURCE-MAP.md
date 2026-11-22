# Paper 16: literal lambda and auxiliary child provenance on one shared V

Status: frozen source, native gates pending. Queue
`exact_OpenCoverSharedMemoRowCases`, `exact_OpenCoverSharedMemoEarlierValue`,
`exact_OpenCoverSharedLambdaSyntaxParent`, and
`exact_OpenCoverSharedAuxSyntaxParent` as split roots.

Generic physical row cases on exactly one selected updater R derive the
original predecessor table and its actual next step with the exact given
parent output. No old table is provided; arithmetic Program totality picks
the two actual witnesses, and original same-table successor and graph
functionality agree on that table/next update at the parent. The earlier
lookup lemma retains R and the physically observed old table, exact field
selection and strict smaller address; original thin memo lookup requires
that very table. It returns the selected child's actual value, not an
evaluation numeral reflected into a derivation. Arbitrary output supports
both syntax and measurement applications; no particular R is presumed.

The literal tag-2/6 parent roots instantiate R with sharedSyntaxUpdate.
The checked dispatch reductions cut only the actual current step at its
literal left/two-field or right/four-field tape. Actual child slots and
earlier guards are then recovered on that current tape. Both branches read
the **same shared R** earlier table for their children, not either
former individual updater. Lambda retains genuine annotation type bit and
body acceptance; auxiliary retains both genuine type bits and both child
acceptances. No numerical equalities, unchanged old V, broad arbitrary
raw header recognition, typed W, grammar/measure or own-cover conclusion.

## Frozen sources
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedMemoTargets.lean`: `c25242274048548dee8d358d47f2b47720233caf9d77f48df331199072b248e1`, 1129 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedMemoRowCasesProof.lean`: `d9786169808be89ad0ca65c81e0ba22692e335ccd51c1e9a8d644e11ae94dec9`, 1265 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedMemoLookupProof.lean`: `defb6dc2ba8ade2fbd1c3f02af05e680e2b1195c0e64cbc0a7ec44c36f29568f`, 1275 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedLambdaSyntaxProof.lean`: `5b62f0f3b2cc09864ea989fb4907f2e8cbfb66ee79b826d55dece08738fda144`, 1286 local modules.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedAuxSyntaxProof.lean`: `7c04e4625794ea9c9f646c8af6523d84341bd987f7c1f7235468a88d91996953`, 1306 local modules.
No explicit Hydra or Linarith in these static local import closures.

## Principal exact origin pins
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedRecursionTargets.lean`: `5373766077ea0b7d34b57522fc83d828eba7b828253c74c615541b7270d46404`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverSharedRecursionOpenCutProof.lean`: `0bdb91db432cfcf9e783e5abdbf5b52150fea1264c234e8189f6435e43739f93`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxMeasureOpenThinSlotProof.lean`: `b05844bf318e4e15547881cb1d75042f8f4fe4f56727df2bd8637d4facb3f1b0`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAuxMeasureOpenDataProof.lean`: `43153b983eecf710e1d58cbb9065ef55d14ffd8d4b85f359d3b920b456bc039c`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalScratchMemoThinSuccessorProof.lean`: `1a8dfe73356a1915c638a9adfe38b0c8298139ff6a11c98abbcbc94948333ba7`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof.lean`: `717c863324e5effc3544c169eb6119f6bd9bca185b2e6a712f486f8e3087d298`.
- `formalization/LogicLineages/PersistentMarking/NumberedWindowInternalCoverAuxSyntaxOpenRowProof.lean`: `9a123541add95cd506fc1b14eafd18d82f45c4563a15a11a2ac38f104072fe95`.
