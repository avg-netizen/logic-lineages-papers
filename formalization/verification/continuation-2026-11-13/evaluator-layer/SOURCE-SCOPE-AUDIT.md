# Evaluator layer source-scope audit

Status: independent source review complete; coordinator confirmed final `exactSourceUnfolding` native PASS, receipt `1794567579558238596-5`. Evidence verification remains pending. This source audit is not a replacement for the native receipt or axiom audit.

## Exact endpoint

`EvaluatorLayerTargets.ActualSourceUnfolding` quantifies arbitrary original programs `R,H,G,M,W`, internal formula/context/types, packed input, parameter and output. Its sole supplied derivation is the literal original `source H G M W = 1` graph. It concludes an internal graph iff between the unchanged `evaluator R` and unchanged `layer R (evaluator R)`, at the **same output, packed input and parameter**.

No external framed-completion, child-content, semantic row, fuel bound, Expected predicate, native calibration, or fixed-point equation is an endpoint premise. The output is arbitrary, not a preselected semantic value.

## Supplier discharge

1. `SourceLayerQueries.sourceCases` queries actual codec/program coordinates and obtains root admission, term acceptance, branching and weight from the original source graph through original initialization/acceptance lemmas. Its CPS continuation does not assume the desired iff.
2. `SourceLayerRootProof.fromRoot` queries actual child/deletion counts, frames, annotated expansion, tagged agenda, mapped observation row, reverse produced row and length. Unconditional internal below-weight completion and below-weight content theorems supply admitted descendants' execution and content. These facts are derived, not endpoint hypotheses.
3. `SourceLayerRowsProof.fromRows` combines actual finite mapped visits with ordinary finite completion. Produced-row uniqueness pays its exact length, and the actual expansion length pays the child-plus-deletion count. The prefix count is internally eliminated from actual Counted execution.
4. `SourceLayerReturnProof.fromPrefix` obtains an actual uniform return value from original admission, counters and produced length. `fromReturn` uses that same value for both: (a) `UniformTermLayerProof.actual`, retaining the original R and selecting Q = evaluator R; (b) exact visit-prefix-return composition and original computed-fuel evaluator identification through `FramedTermQueries.evaluatorValue`.
5. `GraphSharedValueProof.iffAt` constructs both directions solely from graph functionality and output transport at this shared value. It does not take an iff premise.

## Program and circularity checks

The referenced original layer remains `pair(rootObservation R, pair(rootObservation Q, rows Q))`. The original evaluator remains the head projection of the original computed-fuel runtime, not a substituted recursive observer. The proof files contain no replacement evaluator/layer definition.

Import-closure checks found no dependency on final `EvaluatorLayerProof` from `FramedContentProof`, `SourceFramedProof`, or `UniformTermLayerProof`. Reading the displayed proof calls found no appeal to a desired layer iff, native semantic fixed-point theorem, or Expected supplier. Importing a target declaration in a generic functionality helper does not assert that target.

## Limitations

The accepted endpoint establishes source-admitted internal graph unfolding. It does not by itself assert old-representative equality, native calibration, primary-equivalence completeness, covariance, or a fixed-point property for malformed/unadmitted inputs. The coordinator reported the native endpoint PASS above; closure/evidence verification remains separately tracked. This document does not independently certify that verification.

## Reviewed source fingerprints

- `EvaluatorLayerTargets`: `f8e76ecc9b4368a05440fd36e7442490112152a08f6fecf8e33119d22344c77b`
- `SourceLayerQueries`: `e6f51f63f81420f8f34e319d055e13854658b78ed92d6d6e6d995036395db218`
- `SourceLayerRootProof`: `8ba724a5b667746f22f897dc673238f645e013fa83f10f813658b672c28c17cf`
- `SourceLayerRowsProof`: `055a9cbc0c5c90b99175c35e45d99f8be7db2c086db323a03fb497a69764840c`
- `SourceLayerReturnProof`: `692bcc420f7314ee4987f1edfd4340d5159e8874619a56b66ba9165597a856f3`
- `EvaluatorLayerProof`: `6424baa6dc62444603c45a9f7b3041dced5f1082a493a4e7b9dbf9c740042da4`
- `GraphSharedValueProof`: `87a6adb5a5387a1dda63d55583b32df101b550e63f56fdbc4d7a7a367e517209`
- `UniformTermLayerProof`: `518c7eb0ccaaea16bca1c2badfaa685bb480094c5f3ddb4a012ca2e15477095f`
