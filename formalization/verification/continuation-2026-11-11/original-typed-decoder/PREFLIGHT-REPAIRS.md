# Preflight repairs

Attempt 1: coordinator receipt 1794401426418076234-5. ValuesDefinitions and
Definitions passed and remain byte-identical. StepSpecification failed solely
because `existsOne` was not opened. Targets and Preflight were not attempted.
The complete original five-file packet, original hashes/source correspondence/
status, and all attempt logs/receipt are preserved in preflight-attempt1/.

Repair: add `existsOne` to the existing selective open of
SourceComputabilityFormulaSupportProof in StepSpecification. No AST, formula,
target or mathematical meaning changes. Refresh FROZEN-SHA256SUMS and await
coordinator preflight before any proof.
