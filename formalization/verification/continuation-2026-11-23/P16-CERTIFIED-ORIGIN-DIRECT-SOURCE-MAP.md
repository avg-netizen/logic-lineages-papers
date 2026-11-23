# Paper 16: literal numeric checker on each changed component

Paper 16, `sections/ordinals.tex`, lines 143–153, splits an original
replacement on a component union into changes on the left, right, or
both, with at least one changed component. The exact statement here
starts with the actual source-union permutation and an accepted
`NumberedWindowDirectAlgorithm.directLists` call on the actual whole
source, target and row witness. It does not assume scalar typing or
side acceptance beyond what is tested by that call.

The numeric proof uses the checked occurrence split, original-row
assignment, and original-target projection. On each side whose
removed tape is nonempty it reconstructs a genuine witness accepted
by the same `directLists` with the same scalar and positive checks.
When the removed tape is empty it contains no possible dominator,
so its inserted tape is empty too. Use that component's identical
original ordered source list in the output, not its potentially
reordered residual tape. The recombination report still describes the
same original target up to the genuine occurrence permutation.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginDirectProof`,
alias `exact_NumericOriginDirectCases`. Does not pack raw tag-5 or tag-4
certificates, reconstruct raw side terms/reports, or prove the
arbitrary-open arithmetic `CertifiedOriginSplit`.

Frozen Lean source hashes (SHA-256):

    9eb176df431284016cc48b10c0d05b1ddc4f43b6452349974be8d7239814e639  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginDirectProof.lean
    a1f19c98eb916ea34373590e996bb3c56c3aaa8ac76fa02b2d231468fcb23789  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginDirectTargets.lean
