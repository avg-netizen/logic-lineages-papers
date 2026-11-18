# Namespace-only repair review

Approved proposed sole edit: `def data (F : Inputs S)` to `def Inputs.data (F : Inputs S)`, retaining the complete type and RHS. Current source is byte-identical to the preserved failing edition under receipt 1795005024867578724-2. The log identifies unresolved F.data field notation: the intended declaration must reside in the Inputs namespace for this notation.

This changes declaration qualification only, not the inventory construction, state predicates, six motives or exact targets. Preserve original freeze and failure; refresh only the PortNormalization.lean pin after applying the one-line edit, and independently confirm applied diff and all other eight pins before a fresh parent-granted retry. No proof acceptance or cap change.

Applied confirmation: exact single declaration-qualification edit verified against preserved source; only one of nine pins changed, to 59de67cc28603f0fabf9183f28540cbb5909545145c9f94aebac0781a3937f8f. All nine current hashes verify. Eligible for parent-granted retry, no proof acceptance.
