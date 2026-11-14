# Original finite-pool uncovered-occurrence potential: exact4

Frozen before proof. This is an auxiliary proof measure on the existing actual numeric lists, NOT a changed reachability algorithm, deduplicated pool, or replacement cutoff.

Actual source: ContextUniformPrimaryDefinitions.lean defines vertices = q :: candidates and primaryList = reachable at (vertices ...).length. Its step appends a filter of the SAME pool, tested against OLD reached. Consequently raw reached list lengths can keep growing through duplicates even when membership stabilizes; using reached length as strict progress would be unsound.

Instead count(pool,reached) right-folds the original pool, adding one for each occurrence whose actual contains acceptance fails. Repeated vertices count repeatedly, so count is bounded by literal pool length. The countStep branch order follows InternalAcceptance.branch: zero/rejection adds one, one/acceptance retains tail count. Generic non-one branch is normalized exactly as existing internal controls.

Exact4: (1) native all-code calibration to literal filter-not-member length; (2) internal upper bound by the already paid OriginalContextInsertion.length graph, which counts actual cons cells; (3) internal antitonicity for actual object-language inclusion; (4) internal strict decrease when an explicit actual pool member was absent and becomes present. Both counts are actual graph outputs. Newness is a derivation of negated membership, not a metalevel non-derivability or native decision assumption.

Proof plan: native actual raw-list fold calibration, separately internal strong induction on pool code. At each genuine cons, query both tail counts, split actual contains acceptance and use arithmetic successor order. Strict decrease splits whether the new candidate is the head; otherwise actual contains miss recovers a tail witness and applies strict induction. Reuse paid internal raw-list decomposition, membership hit/miss, and ordinary order arithmetic.

Still unpaid: internal stabilization at the selected literal vertices.length cutoff, deriving a new-member witness from failure of closure, selected count/pool correspondence inside arithmetic, internal original edge correctness, and class coherence. Native calibration is never used as an internal premise. The explicit newness and inclusion premises of the generic strict theorem are proof prerequisites, not hidden claims about a completed original run. No original operator or target is modified.

No proofs authored, no compiler launched; awaiting independent review and preflight.
