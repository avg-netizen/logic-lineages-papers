# LiteralRawMP native and occurrence subset accepted

Coordinator reports NativeProof (7 audited declarations) and NativeStatementChecks exact2 PASS, standard axioms only, within receipt `1794590592077872717-5`. The overall queued run later failed in the independently owned constructor module: this is NOT a whole-packet pass. ActualChildren/Occurrence exact1 passed earlier in `1794590294518597556-5`. The four listed sources are now immutable; their author hash snapshot is attached separately from coordinator evidence.

Exports: `NativeProof.nativeRaw`, `NativeProof.nativeEven`, `OccurrenceProof.actualChildren`.

NativeRaw proves all-vector equality for the literal line and constructor ASTs against the original raw formula/certificate decode/default definitions. The proof establishes codec totality rather than assuming successful decode, reuses actual pair/cons/list-append/length evaluation, and retains the original implication-then-antecedent-then-new-line order and antecedent-length implication reference.

NativeEven identifies this constructor with mpCertificate ONLY on canonical even sorted formula codes `formulaRawNumber raw`, with raw input `Encodable.encode raw`. No odd/default formula specialization is asserted.

ActualChildren proves genuine syntactic occurrences of lengthProgram and lineProgram in this exact constructor using Occurs and taggedCoverage, not extensionally equal substitute Programs.

Native evaluation is not used as an internal inference rule. Internal constructor/reference/dispatcher proofs remain owned by the history lane and have separate verification status. No full MP closure, new-line validity elimination, HB/collapse, or paper completion is claimed. Frozen Definitions/Targets/Preflight unchanged; failed native drafts remain archived.
