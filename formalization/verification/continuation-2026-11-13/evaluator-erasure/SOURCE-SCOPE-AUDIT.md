# Evaluator erasure and deletion-chain scope audit

## Status

Independent read-only source audit: no scope mismatch or hidden semantic supplier found. EvaluatorErasure exact gate passed per coordinator receipt `1794568297347946997-5`; evidence verification is not independently certified here. DeletionChain native gate was running when assigned and remains pending coordinator confirmation. No compiler or proof-source edits performed by this reviewer.

## Exact erasure result

`ActualErasureCongruence` preserves `AdmittedPair`: both original `OriginalUniverseDecoder.source H G M W` tests and an internally existential common output of the unchanged `OriginalHereditaryEvaluatorDefinitions.evaluator R`. The original evaluator still uses the original computed fuel, runtime iteration, and result-stack head projection. R, H, G, M, W remain unchanged throughout.

The initial pair's source acceptance and common evaluator output are explicit, necessary premises. Neither erased source acceptance nor a common output after erasure is assumed. The other premises are actual parameter pairings, current context length, in-range cutoff, literal selected-type lookup, actual deleteAt graph, and actual erasePackedRaw graphs for both inputs. They are not an assumed semantic insertion or a transformed equality.

`EvaluatorErasureQueries.atCommon` internally queries the common output's two pair levels and its deletion-row cell, reconstructing both pairs from actual projections. `RowProof.rowAt` applies the already proved source-only evaluator/layer equation and original layer recovery to recover the same hereditary row for both inputs. `cellAt` applies original in-range indexed-row semantics. `ObservationProof.actualCell` opens the original observation composition at literal erasure and parameter-selector graphs, deriving evaluator output at each erased input. It does not reflect a native evaluator equation.

`Core.atCoordinates` derives actual insertion from length, bound, delete and lookup using `OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion`. Original packed-source erasure then derives both new source tests. Finally the selected common row cell is existentially introduced as the new common evaluator output. That output need not equal the original common output; the preserved relation is equality between the two evaluations at the new parameter.

## Finite-chain boundary

`DeletionChain.Transition` bundles only eight operational graphs/bounds: current/next parameters with the same outer window, current length and cutoff bound, selected-type lookup, context deletion, and the two actual erasures. It contains no source-admission or evaluator-equality assertion.

`ActualFiniteChain` assumes AdmittedPair only at index zero and transitions at every finite index. The proof uses external Nat induction, restriction to the prefix, and one final checked erasure step. Intermediate admissions/common outputs are derived. The endpoint is the same relation at the final index.

This is a family of internal derivations indexed by external finite length, not a single internal coded-trace induction theorem. It does not prove existence of a legal deletion sequence, equality of arbitrary observer families, equality of raw or canonical Object syntax, selected-fold fixedness, or preservation of the original numeric output across deletions. The explicit target comments respect these boundaries.

## Source fingerprints

- `DeletionChainDefinitions.lean`: `31398ed929f7f2fed3461d4d45cabaf4f938e33f2feb7c2a096b3b4b2fd06aae`
- `DeletionChainPreflight.lean`: `7bd8c008f808cecc8ac71d6369dacef6b38fd029f17450cd2f138a6a30330aed`
- `DeletionChainProof.lean`: `6f68520b6b80571f679c0a3761f8ffe0b06b6a9e32693d914ab75ba28ffb9c6e`
- `DeletionChainStatementChecks.lean`: `aef54b8741844ca136a0248bce9435fe3850f6a446fe614d9fa0e3582ef1bac7`
- `DeletionChainTargets.lean`: `93c8cdcb14e74e2b02dd2cd9d3e9714e16c82fd7a17799706e279a334a495d04`
- `EvaluatorErasureCore.lean`: `0552840557477fb1540136413fda3bf90d25882b73dff096c31dbd8bb95426c3`
- `EvaluatorErasureDefinitions.lean`: `b9b9300c3012d6d3dfa6950f216526a0d5905910a3c3b9cb6db474d5e8679597`
- `EvaluatorErasureObservationProof.lean`: `25fec2b7a78fd3b9d33c2c72c98a5c453b9bd58d6d53a018d66619970a5f5da7`
- `EvaluatorErasurePreflight.lean`: `76e589b23c54beed0fbf4fa9693e1a98ecc43f0bd73ed4a53360745514418360`
- `EvaluatorErasureProof.lean`: `59e2000889a04149f4199fc350fc9bac70effab9552bf190675a06fe801318f9`
- `EvaluatorErasureQueries.lean`: `cbf7ddfdf56d5be5f62586ad4387636b402d8938548263942bacc42116971f53`
- `EvaluatorErasureRowProof.lean`: `ed8f559c5b286950e10f087360edab787b44afe7f783673b23b7a4f1dec84cc3`
- `EvaluatorErasureStatementChecks.lean`: `acfa395e43b53feb5e78f7d5f8c4ebb69cf3cc8e128ef64fa81d70262832f89c`
- `EvaluatorErasureSyntax.lean`: `6c9c947be1aa4542b721d44e46c14ea07c6062387ff89462c4670f382398f801`
- `EvaluatorErasureTargets.lean`: `de697723352a2af97fd8c11127d2ad983b44d9185653c7203f8ba649b1df6fb7`
