# Finite decomposition of direct occurrence replacement

Paper06 lines598–603 assigns each inserted occurrence to a removed dominator. This component connects the already accepted simultaneous Direct R replacement to literal finite sequences of Mathlib Relation.CutExpand, without replacing Direct by a closure definition.

R is source-to-successor. The library relation is CutExpand (fun successor source => R source successor) target source. CutPath records a forward source-to-target sequence, with precisely one removed occurrence per step. The dominated-occurrence target counts exactly removed.length, including zero for empty removal; Direct's nonempty removal yields a positive count.

All lists are coerced to multisets with multiplicity retained. Kept occurrences persist; each inserted occurrence is assigned to some removed occurrence; one dominator may support many inserts; empty assigned buckets are deletion steps. Neither set conversion nor cancellation of duplicated occurrences is allowed. The proof must derive an occurrence partition, not assume it.

No irreflexivity, Preorder, transitivity or well-foundedness premise is imposed on R. This is finite path decomposition only: no accessibility or transitivity theorem, no equivalence between arbitrary CutPath and Direct, and no ID1 claim. Parent released exact comparator/freeze and finite proof after review on 2026-11-04 10:40 UTC. Export/publication still require separate release.
