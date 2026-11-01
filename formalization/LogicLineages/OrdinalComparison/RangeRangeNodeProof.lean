module
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedProof
public import LogicLineages.OrdinalComparison.RangeRangeNodeEqualProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

private theorem last_split (word : List (NONote × Nat)) (hne : word≠[]) :
    ∃ (pre : List (NONote × Nat)) (eta : NONote) (c : Nat),word=pre++[(eta,c)] := by
  cases hr : word.reverse with
  | nil =>
    have h := congrArg List.reverse hr
    simp only [List.reverse_reverse,List.reverse_nil] at h
    exact (hne h).elim
  | cons p rest =>
    rcases p with ⟨eta,c⟩
    refine ⟨rest.reverse,eta,c,?_⟩
    have h := congrArg List.reverse hr
    simpa only [List.reverse_reverse,List.reverse_cons] using h

theorem correct : Targets.ActualRangeRangeQueryNodeCorrect := by
  intro word other E F hR hS leftProfile rightProfile table
  dsimp only
  intro hc
  obtain ⟨w,eta,c,hw⟩ := last_split word hR.1
  obtain ⟨v,lower,d,hv⟩ := last_split other hS.1
  subst word other
  by_cases heq : eta=lower
  · subst lower
    exact equal_correct w v eta c d E F hR hS leftProfile rightProfile table hc
  · let q : ComparisonQuery := ((oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(lower,d)]) F)),(leftProfile,rightProfile))
    let N := max (encodedComparisonTableTail table) (encodedRangeRangeLocalTail q)
    have hresult : encodedRangeRangeQueryNode q table=
        (encodedSourcePairSignAt (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
          (oneVariableComparisonEncode (.range (v++[(lower,d)]) F)) N,N) := rfl
    rw [hresult]
    have hNT : encodedComparisonTableTail table≤N := Nat.le_max_left _ _
    have hNL : encodedRangeRangeLocalTail q≤N := Nat.le_max_right _ _
    have hN1 : 1≤N := (ComparisonNode.table_tail_positive table).trans hNT
    have hDomR : oneVariableComparisonDomainBound (.range (w++[(eta,c)]) E)≤N := by
      rw [←(OneVariableComparison.source_program.2.2 _ hR).1]
      exact (left_domain_bound q).trans hNL
    have hDomS : oneVariableComparisonDomainBound (.range (v++[(lower,d)]) F)≤N := by
      rw [←(OneVariableComparison.source_program.2.2 _ hS).1]
      exact (right_domain_bound q).trans hNL
    by_cases hlt : lower.1.repr<eta.1.repr
    · have hMixed := mixed_pair q w v eta lower c d E F hR hS (Or.inl rfl) hlt table hc N hNT hNL
      have hs : comparisonEventualSignData (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F)
          (encodedSourcePairSignAt (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
            (oneVariableComparisonEncode (.range (v++[(lower,d)]) F)) N,N) :=
        ComparisonNode.point_tail_from_stable _ _ hR hS N hN1 hDomR hDomS hMixed.1
      intro E' F' hEc hFc hEV hFV
      have hEq : E'=.range (w++[(eta,c)]) E := ComparisonExpansion.source_injective hEc
      have hFq : F'=.range (v++[(lower,d)]) F := ComparisonExpansion.source_injective hFc
      subst E' F'
      refine ⟨hs,?_,?_⟩
      · intro hSig
        exact hMixed.2.1 leftProfile (by simp [q]) (fun x hx => (hs.2.2 x hx).2.2.2.2.mp hSig)
      · intro hSig
        exact hMixed.2.2 rightProfile (by simp [q]) (fun x hx => (hs.2.2 x hx).2.2.1.mp hSig)
    · have hgt : eta.1.repr<lower.1.repr := by
        apply lt_of_le_of_ne (le_of_not_gt hlt)
        intro hr
        exact heq (Subtype.ext (ONote.repr_inj.mp hr))
      have hMixed := mixed_pair q v w lower eta d c F E hS hR (Or.inr rfl) hgt table hc N hNT hNL
      have hs : comparisonEventualSignData (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F)
          (encodedSourcePairSignAt (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
            (oneVariableComparisonEncode (.range (v++[(lower,d)]) F)) N,N) :=
        ComparisonNode.point_tail_from_stable _ _ hR hS N hN1 hDomR hDomS
          (fun x hx => ComparisonNode.natural_sign_swap _ _ _ _ (hMixed.1 x hx))
      intro E' F' hEc hFc hEV hFV
      have hEq : E'=.range (w++[(eta,c)]) E := ComparisonExpansion.source_injective hEc
      have hFq : F'=.range (v++[(lower,d)]) F := ComparisonExpansion.source_injective hFc
      subst E' F'
      refine ⟨hs,?_,?_⟩
      · intro hSig
        exact hMixed.2.2 leftProfile (by simp [q]) (fun x hx => (hs.2.2 x hx).2.2.2.2.mp hSig)
      · intro hSig
        exact hMixed.2.1 rightProfile (by simp [q]) (fun x hx => (hs.2.2 x hx).2.2.1.mp hSig)

theorem full : Targets.FullActualRangeRangeQueryNode := ⟨limit_fixed,program,correct⟩

end LogicLineages.OrdinalComparison.RangeRangeNode
