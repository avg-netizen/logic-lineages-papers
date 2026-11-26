# Literal association-graph stage, exact4
Source: Mathlib/Computability/Primrec/List.lean nat_omega_rec' lines 305–362,
specifically graph successor filterMap at lines 315–316. Each frontier node is
evaluated from the SAME old association graph; it does not see newly produced
entries. D supplies the literal ordered dependencies. ExchangeMapGraph retains
first-match lookup and omits missing keys. G supplies the optional layer answer.
None nodes are omitted; Some values are paired with their original numeric node.
Order and duplicates of frontier and dependency lists are unchanged.

NativeStage calibrates the actual Program AST to this literal filterMap using
explicit native D/G calibration hypotheses. It assumes neither graph completeness
nor successful layer answers. NativeCoveredMap separately states the legitimate
coverage condition allowing mapGraph to become a full map. This is a native list
theorem, not internal semantic reflection.
InternalSkip and InternalKeep compose actual internal D, mapGraph, G, pairing,
cons and stage graphs. They remain valid for arbitrary terms in arithmetic and
are not inferred from NativeStage.

Still unpaid: literal bindList iteration and original rank-indexed graph recursion,
internal coverage/first-match coherence at every stage, actual dependency supplier
and recursive optional layer installation, headMove semantics and original E
correctness. No dense-row substitution, changed rank or cutoff, full recursive E,
or original P6/class-coherence completion is claimed. Existing full tuple remains
unchanged. Frozen files must not change after review except explicitly tracked
elaboration repairs.
