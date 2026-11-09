module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmDomainsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmTerminalSignProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

theorem partition_branch_domain_correct (D maximum : Nat) (r : Row)
    (hDegree : 3 ≤ D) (hD : RowAllowed D r)
    (hm : hasMaximum maximum (canonicalRow r) = true) (labels : List Nat)
    (hl : labels ∈ assignments (active (canonicalRow r)).length (active (canonicalRow r)).length)
    (ν : Nat → Nat) (hr : Region (stageCutoff D maximum r) maximum (rowVariables r) ν)
    (hd : RowDomain r ν) :
    let out := partitionBranch D maximum (canonicalRow r) labels
    let b : Branch := {out with tail := max (rowTail r) out.tail}
    BranchDomains b ν ∧ BranchCorrect maximum r b ν := by
  have hcurrent := region_current _ maximum r ν hr
  have hptail := partitionTail_le_stageCutoff D maximum r hm labels hl
  have hpartition : ∀ a ∈ active (canonicalRow r),
      partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum := by
    intro a ha
    have hc := hcurrent a (List.mem_filter.mp ha).1
    exact ⟨hptail.trans hc.1,hc.2⟩
  have hsource : ∀ a ∈ active (canonicalRow r), sourceTail a ≤ ν a.2.1 := by
    intro a ha
    exact (rowSourceTail_source _ a ha).trans ((Nat.le_max_left _ _).trans (hpartition a ha).1)
  have hf := partitionGuard_facts D maximum r labels hDegree hD ν hpartition
  have hcanonical := canonical_value D r ν hD hd
  cases hz : zeroClass (canonicalRow r) labels with
  | some removed =>
      have hs := zeroClass_some_data (canonicalRow r) labels removed hz
      have hlen := ((assignments_membership _ _ _).mp hl).1
      simp only [partitionBranch,hz,BranchDomains,BranchCorrect]
      refine ⟨⟨hf.2.1,rewrite_domain D r labels removed hDegree hD ν hd hsource⟩,?_⟩
      intro hg
      exact (actual_zero_class_identity D maximum r labels hDegree hD hlen removed
        hs.2.1 hs.2.2 ν hpartition hg).trans hcanonical
  | none =>
      have hstail := signTail_le_stageCutoff D maximum r hm labels hl hz
      have hsign : ∀ a ∈ active (canonicalRow r), signTail (canonicalRow r) ≤ ν a.2.1 := by
        intro a ha
        exact hstail.trans (hcurrent a (List.mem_filter.mp ha).1).1
      simp only [partitionBranch,hz,BranchDomains,BranchCorrect]
      refine ⟨⟨hf.2.1,by simp [RowDomain]⟩,?_⟩
      intro hg
      have hs := terminal_partition_strict D maximum r labels hDegree hD hl hm hz ν
        hpartition hsign (fun a ha => (hcurrent a ha).2) hg
      unfold OutcomeCorrect
      by_cases hneg : leading ((classes (canonicalRow r) labels).getLastD []) < 0
      · refine Or.inl ⟨by simp only [if_pos hneg],?_⟩
        have hvalue := hs.1 hneg
        rwa [hcanonical] at hvalue
      · refine Or.inr (Or.inl ⟨by simp only [if_neg hneg],?_⟩)
        have hvalue := hs.2 hneg
        rwa [hcanonical] at hvalue

theorem exactStageSemantics : AlgorithmTargets.ExactStageSemantics := by
  intro D maximum r hDegree hD ν hr
  have hd : RowDomain r ν := rowTail_domain D r ν hD (by
    intro i hi
    exact (originalTail_le_stageCutoff D maximum r).trans (hr i hi).1)
  refine ⟨hd,?_,?_,?_⟩
  · intro b hb
    by_cases hm : hasMaximum maximum (canonicalRow r) = true
    · obtain ⟨labels,hl,rfl⟩ := List.mem_map.mp (by simpa [stage,hm] using hb)
      exact (partition_branch_domain_correct D maximum r hDegree hD hm labels hl ν hr hd).1
    · have he : b = ⟨max (rowTail r) (rowSourceTail (canonicalRow r)),.top,
          .finish ⟨3,canonicalRow r⟩⟩ := by simpa [stage,hm] using hb
      subst b
      refine ⟨?_,canonical_domain r ν hd⟩
      simp [Formula.meaningful,Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
  · by_cases hm : hasMaximum maximum (canonicalRow r) = true
    · let labels := witnessLabels (active (canonicalRow r)) ν
      have hl := witnessLabels_admitted (active (canonicalRow r)) ν
      let out := partitionBranch D maximum (canonicalRow r) labels
      let b : Branch := {out with tail := max (rowTail r) out.tail}
      have hb := partition_branch_member D maximum r hm labels hl
      have hcurrent := region_current _ maximum r ν hr
      have hptail := partitionTail_le_stageCutoff D maximum r hm labels hl
      have hpartition : ∀ a ∈ active (canonicalRow r),
          partitionTail D maximum (canonicalRow r) ≤ ν a.2.1 ∧ ν a.2.1 ≤ ν maximum := by
        intro a ha
        have hc := hcurrent a (List.mem_filter.mp ha).1
        exact ⟨hptail.trans hc.1,hc.2⟩
      refine ⟨b,hb,?_⟩
      have hg : Formula.eval ν (partitionGuard D maximum (canonicalRow r) labels) := by
        apply (partitionGuard_facts D maximum r labels hDegree hD ν hpartition).2.2.2.mpr
        intro a ha c hc
        exact (witness_pair_order (canonicalRow r) ν a c ha hc).symm
      cases hz : zeroClass (canonicalRow r) labels <;>
        simpa [b,out,partitionBranch,hz] using hg
    · refine ⟨⟨max (rowTail r) (rowSourceTail (canonicalRow r)),.top,
        .finish ⟨3,canonicalRow r⟩⟩,?_,True.intro⟩
      simp [stage,hm]
  · intro b hb
    by_cases hm : hasMaximum maximum (canonicalRow r) = true
    · obtain ⟨labels,hl,rfl⟩ := List.mem_map.mp (by simpa [stage,hm] using hb)
      exact (partition_branch_domain_correct D maximum r hDegree hD hm labels hl ν hr hd).2
    · have he : b = ⟨max (rowTail r) (rowSourceTail (canonicalRow r)),.top,
          .finish ⟨3,canonicalRow r⟩⟩ := by simpa [stage,hm] using hb
      subst b
      intro hg
      exact Or.inr (Or.inr ⟨rfl,canonical_maximum_absent maximum r
        (Bool.eq_false_of_not_eq_true hm),canonical_value D r ν hD hd⟩)

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
