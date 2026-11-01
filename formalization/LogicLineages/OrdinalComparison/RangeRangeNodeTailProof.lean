module
public import LogicLineages.OrdinalComparison.RangeRangeNodeProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

attribute [local irreducible] encodedRangeRangeNormalization encodedComparisonOuter

abbrev eta_candidates (q : ComparisonQuery) : List Nat :=
  [(encodedComparisonOuter q.1.1).1,(encodedComparisonOuter q.1.2).1,(encodedRangeRangeNormalization q.1).2.1]

private theorem fold_positive (values : List Nat) : 1≤values.foldr max 1 := by
  induction values with
  | nil => exact le_rfl
  | cons n values ih => exact ih.trans (Nat.le_max_right _ _)

private theorem fold_member (values : List Nat) (n : Nat) (hn : n∈values) : n≤values.foldr max 1 := by
  induction values with
  | nil => cases hn
  | cons m values ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · exact Nat.le_max_left _ _
    · exact (ih hn).trans (Nat.le_max_right _ _)

theorem tail_positive (q : ComparisonQuery) : 1≤encodedRangeRangeLocalTail q := fold_positive _

theorem tail_member (q : ComparisonQuery) (n : Nat) (hn : n∈encodedRangeRangeLocalTails q) :
    n≤encodedRangeRangeLocalTail q := fold_member _ n hn

theorem left_domain_bound (q : ComparisonQuery) :
    encodedOneVariableComparisonDomainBound q.1.1≤encodedRangeRangeLocalTail q := by
  apply tail_member q
  unfold encodedRangeRangeLocalTails
  exact List.mem_append_left _ (List.mem_cons_self)

theorem right_domain_bound (q : ComparisonQuery) :
    encodedOneVariableComparisonDomainBound q.1.2≤encodedRangeRangeLocalTail q := by
  apply tail_member q
  unfold encodedRangeRangeLocalTails
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem normalization_tail_bound (q : ComparisonQuery) :
    (encodedRangeRangeNormalization q.1).2.2≤encodedRangeRangeLocalTail q := by
  apply tail_member q
  unfold encodedRangeRangeLocalTails
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem normalization_domain_bound (q : ComparisonQuery) :
    encodedOneVariableComparisonDomainBound (encodedRangeRangeNormalization q.1).1≤encodedRangeRangeLocalTail q := by
  apply tail_member q
  unfold encodedRangeRangeLocalTails
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self))))

private theorem scalar_member (q : ComparisonQuery) (eta : Nat) (hEta : eta∈eta_candidates q)
    (n : Nat) (hn : n∈encodedRangeRangeKernelTails eta
      (encodedComparisonOuter q.1.1).2 (encodedComparisonOuter q.1.2).2 [q.2.1,q.2.2,1]) :
    n≤encodedRangeRangeLocalTail q := by
  apply tail_member q
  unfold encodedRangeRangeLocalTails
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨eta,hEta,hn⟩)

theorem mass_bound (q : ComparisonQuery) (eta : Nat) (hEta : eta∈eta_candidates q) :
    encodedPrincipalKernelMassModulus eta (encodedComparisonOuter q.1.1).2 (encodedComparisonOuter q.1.2).2≤
      encodedRangeRangeLocalTail q := by
  apply scalar_member q eta hEta
  unfold encodedRangeRangeKernelTails
  exact List.mem_append_left _ (List.mem_singleton_self _)

private theorem profile_entry (eta c d : Nat) (profiles : List Nat) (P : Nat) (hp : P∈profiles)
    (n : Nat) (hn : n∈[encodedLimitPairCertificateTail eta P c d,encodedLimitPairCertificateTail eta P d c,
      encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P c,
      encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P d]) :
    n∈encodedRangeRangeKernelTails eta c d profiles :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨P,hp,hn⟩)

theorem profile_bounds (q : ComparisonQuery) (eta : Nat) (hEta : eta∈eta_candidates q)
    (P : Nat) (hP : P∈[q.2.1,q.2.2,1]) :
    encodedLimitPairCertificateTail eta P (encodedComparisonOuter q.1.1).2 (encodedComparisonOuter q.1.2).2≤encodedRangeRangeLocalTail q ∧
    encodedLimitPairCertificateTail eta P (encodedComparisonOuter q.1.2).2 (encodedComparisonOuter q.1.1).2≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P (encodedComparisonOuter q.1.1).2≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P (encodedComparisonOuter q.1.2).2≤encodedRangeRangeLocalTail q := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply scalar_member q eta hEta <;> apply profile_entry _ _ _ _ P hP <;> simp

end LogicLineages.OrdinalComparison.RangeRangeNode
