module
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedSetupProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem mass_modulus_symm (eta c d : Nat) :
    encodedPrincipalKernelMassModulus eta c d=encodedPrincipalKernelMassModulus eta d c := by
  simp only [encodedPrincipalKernelMassModulus,Nat.max_comm c d]

theorem mixed_lower_eta (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F)) :
    rawNoteEncode lower.1∈eta_candidates q := by
  rcases hq with hq | hq
  · simp only [eta_candidates,hq,ComparisonExpansion.outer_source]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · simp only [eta_candidates,hq,ComparisonExpansion.outer_source]
    exact List.mem_cons_self

theorem mixed_mass_bound (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (zeta : Nat) (hz : zeta∈eta_candidates q) :
    encodedPrincipalKernelMassModulus zeta c d≤encodedRangeRangeLocalTail q := by
  have h := mass_bound q zeta hz
  rcases hq with hq | hq
  · simpa only [hq,ComparisonExpansion.outer_source] using h
  · simpa only [hq,ComparisonExpansion.outer_source,mass_modulus_symm zeta d c] using h

theorem mixed_profile_bounds (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (zeta : Nat) (hz : zeta∈eta_candidates q) (P : Nat) (hP : P∈[q.2.1,q.2.2,1]) :
    encodedLimitPairCertificateTail zeta P c d≤encodedRangeRangeLocalTail q ∧
    encodedLimitPairCertificateTail zeta P d c≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote zeta) P c≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote zeta) P d≤encodedRangeRangeLocalTail q := by
  have h := profile_bounds q zeta hz P hP
  rcases hq with hq | hq
  · simpa only [hq,ComparisonExpansion.outer_source] using h
  · have hh := h
    simp only [hq,ComparisonExpansion.outer_source] at hh
    exact ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩

theorem mixed_domains (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F)) :
    oneVariableComparisonDomainBound (.range (w++[(eta,c)]) E)≤encodedRangeRangeLocalTail q ∧
    oneVariableComparisonDomainBound (.range (v++[(lower,d)]) F)≤encodedRangeRangeLocalTail q := by
  rw [←(OneVariableComparison.source_program.2.2 _ hR).1,←(OneVariableComparison.source_program.2.2 _ hS).1]
  rcases hq with hq | hq
  · exact ⟨by simpa only [hq] using left_domain_bound q,by simpa only [hq] using right_domain_bound q⟩
  · exact ⟨by simpa only [hq] using right_domain_bound q,by simpa only [hq] using left_domain_bound q⟩

theorem mixed_limit_child (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hl : Order.IsSuccLimit eta.1.repr) (hlt : lower.1.repr<eta.1.repr) :
    (oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F))∈encodedComparisonChildren q.1.1 q.1.2 := by
  rw [mixed_children q w v eta lower c d E F hR hS hq hlt]
  have hne : rawNoteEncode eta.1≠rawNoteEncode lower.1 := by
    intro he
    have hh := congrArg rawNoteDecode he
    rw [rawNoteDecodeEncode eta.1,rawNoteDecodeEncode lower.1] at hh
    exact (ne_of_gt hlt) (congrArg ONote.repr hh)
  dsimp only [encodedComparisonMixedChildren]
  rw [ComparisonExpansion.outer_source,ComparisonExpansion.outer_source,ComparisonExpansion.prefix_program.2,
    limit_fixed w E eta lower c hl]
  simp only [if_neg hne,SourceKernelCalls.program.2,List.mem_singleton]

end LogicLineages.OrdinalComparison.RangeRangeNode
