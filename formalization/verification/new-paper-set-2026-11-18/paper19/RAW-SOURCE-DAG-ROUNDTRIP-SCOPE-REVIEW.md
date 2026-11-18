# Independent bounded typed-roundtrip root scope
Approved RawSourceDAGRoundtripProof development root under six verified frozen pins. Read actual Definitions/Targets and authored proof. Current encoding is newest-first with recursive decoding of tail before step, consistently matching actual Ref indices; this differs from the preliminary oldest-first design but preserves the exact typed graph and backwards references.

Variable/reference induction recovers the same dependent object. Graph induction covers nil and all seven constructors, actual types/local binder prefixes, references and case/recursor payloads. Packed input reconstruction includes context/type/specs/graph/root, not just expanded term semantics. Table length follows actual constructor count, and typedAccepted derives actual decoder success. No sharing loss through unfolding.

This bounded root provides References/TypedRoundtrip plus graph-length and typed-acceptance components only. Validation converse, invalid-tag behavior and genuine Computable valid/reifyCode remain separate final obligations; do not claim all four full targets yet. Scope only, no native executed.
