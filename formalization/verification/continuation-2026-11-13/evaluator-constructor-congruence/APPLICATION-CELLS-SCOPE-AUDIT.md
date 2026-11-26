# Actual application deletion-cell agreement

Coordinator native receipt: `1794588017166716481-33`, full closure passed with standard axioms only.

`EvaluatorConstructorApplicationCellsProof.actualCells` takes only the actual internal `BelowLength R H G M W (suc count)` and literal `applicationFields ... (suc count) xs`. It concludes the original `CellAgreement (evaluator R)` for both parents at the SAME parameter. No parent evaluator equality, desired row equality, caller-provided erased-child equality, compatibility oracle, or native decoding is supplied.

Every bounded cell internally queries the shared original lookup, deleteAt, changed parameter and both erased parents. Four actual child erasures are queried; the original application-erasure adapter rebuilds both erased typed constructors. Actual deletion metadata supplies insertion and the strictly smaller context length. Accepted source erasure and child evaluator-erasure congruence, followed by the genuine smaller-context constructor IH, produce erased-parent agreement. Literal observation opening and the internal all-position binder conclude cell agreement. This is the application successor case, not by itself full constructor congruence or canonical E preservation.

Accepted source hashes:

- `EvaluatorConstructorApplicationCellsChildQueries.lean`: `fbbf36ac5e0419a9f8a0276a6277d1a1f23c1d818913de451880d691013fc1f6`
- `EvaluatorConstructorApplicationCellsCoreProof.lean`: `ed3b656da4890a094b811e383bd9830cd80232d51e0a7282000028b65f1a596b`
- `EvaluatorConstructorApplicationCellsMetadataProof.lean`: `19cfdbb75faa1f91bc9a5a0afe1f7f99c3a2359b28e5082b073e3f77bbb5fab4`
- `EvaluatorConstructorApplicationCellsProof.lean`: `ace984dac871a65d28846430aa7c962eddcf65e98d0c51f26ced6e8dbfbea073`
- `EvaluatorConstructorApplicationCellsRebuildProof.lean`: `bf0b4331944e1aee16799c14c488786f5ff65a8e32996ae03ba009e3137d1872`
- `EvaluatorConstructorApplicationCellsSyntaxProof.lean`: `622150897fd349ed909e137acea711ce55aaf970267b84518640d4edb3ef2252`
