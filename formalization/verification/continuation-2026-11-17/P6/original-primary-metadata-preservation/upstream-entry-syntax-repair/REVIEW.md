# Independent EntryBounds syntax repair review

Approved the exact source bytes recorded in REVIEWED-PINS.json. All eight original theorem headers and attributes are byte-for-byte unchanged. Five untouched original full declarations/proof bodies also match. The changed proof bodies are precisely fieldsSubst, atRawSubst and matrixWitness, which now specialize generic syntax laws. EntryBoundsDefinitions.lean remains byte-for-byte identical to repository HEAD. The original namespace, public imports and audit remain.

The generic fieldsSchema retains the admission graph C at success one, extraction graph X at success (suc entries), and weighted-fold graph W at value/entries, in the original conjunction order. At C=OriginalCodeValidityGuard.check n, W=Fold.weighted(Fold.entryWeight n), X=ArgumentEntriesRecursor.extract, its body exactly matches original fields after whitespace normalization. No admission or successful-extraction guard is removed.

Generic matrixSchema retains Fin 3 coordinates [param,entries,value], the lifted original raw, and conclusion graph1 B value raw. At B=OriginalCodeBoundsRecursion.bounds n, its body exactly matches original matrix. Generic allSchema is the identical allBlock. Both identities were independently checked by normalized source-body comparison. Every old wrapper passes these literal programs in the correct C/W/B/X order.

The generic substitution and matrix-witness proofs apply the existing graph/program substitution, tuple substitution, allBlock binder lifting and witness-lift laws. They assert syntax identities for arbitrary fixed programs, not an arbitrary-program correctness or preservation theorem. No axiom, oracle premise, native reflection, target change, altered raw decoder/default or mathematical weakening is introduced.

This is proof organization intended to reduce concrete-AST elaboration. It merits no substantive-contribution count. No compiler or source edits were made by this review. Native success at unchanged resource limits and recursive evidence remain separate acceptance gates.
