# Paper 16: literal numeric tag-4 and tag-5 direct witness packing

Paper 16, `sections/ordinals.tex`, lines 143–153, requires the
reconstructed components to carry the original kind of replacement
witness. This is the parser/encoder part on the physical numeric
representation. An actual `Entry` is packed with tag 4 and its
ordered target, dominator, and positive certificate unchanged. An
actual `Witness` is packed with tag 5 and the physical kept tape,
removed tape, and packed row tape. Mapping packs each row occurrence
once, in order and with duplicates.

Exact gate `LogicLineages.PersistentMarking.NumberedWindowCertifiedOriginWitnessCodecProof`,
aliases `exact_PackedRow`, `exact_PackedWitness`. The actual original
`readEntry`/`readWitness` parse the produced codes back to the exact
given rows/witness, not up to permutation. This is a right-inverse
statement only. It does not supply a raw derivation on open variables.

Frozen Lean source hashes (SHA-256):

    be59ed963e1120072c337c2bb006a5541e1889b6798f3e5b8e1fcf07682d2994  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginWitnessCodecProof.lean
    2a6d9865894a48921f52b7d09c9a65143a5eb9092e163d868a346c7a16793fc3  formalization/LogicLineages/PersistentMarking/NumberedWindowCertifiedOriginWitnessCodecTargets.lean
