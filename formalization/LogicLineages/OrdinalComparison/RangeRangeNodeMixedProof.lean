module
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedGapProof
public import LogicLineages.OrdinalComparison.RangeRangeNodeMixedPoolProof
public import LogicLineages.OrdinalComparison.RangeRangeNodeSameKernelProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

/-- Entire mixed pair semantics under the actual local induction hypothesis.
The finite normalizer preserves the higher value but never silently transports
an original successor-head profile below a smaller final head. -/
theorem mixed_pair (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hlt : lower.1.repr<eta.1.repr)
    (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (N : Nat) (hNT : encodedComparisonTableTail table≤N) (hNL : encodedRangeRangeLocalTail q≤N) :
    (∀ x : Nat,N≤x →
      comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x)
        (actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x)=
      comparisonNaturalSign (actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) N)
        (actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) N)) ∧
    (∀ profile∈[q.2.1,q.2.2],
      (∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) →
      comparisonBareLimitGap (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F) profile N) ∧
    (∀ profile∈[q.2.1,q.2.2],
      (∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x<
        actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x) →
      comparisonBareLimitGap (.range (v++[(lower,d)]) F) (.range (w++[(eta,c)]) E) profile N) := by
  have hctx := mixed_lower_context q w v eta lower c d E F hq
  have hDom := (mixed_domains q w v eta lower c d E F hR hS hq).2.trans hNL
  have hEta := mixed_lower_eta q w v eta lower c d E F hq
  have hBounds : ∀ profile∈[q.2.1,q.2.2],
      encodedLimitPairCertificateTail (rawNoteEncode lower.1) profile d c≤N ∧
      encodedKernelProfileLeafTail (encodedComparisonPrincipalNote (rawNoteEncode lower.1)) profile d≤N := by
    intro profile hp
    have hh := mixed_profile_bounds q w v eta lower c d E F hq _ hEta profile
      (show profile∈[q.2.1,q.2.2,1] from List.mem_append_left [1] hp)
    exact ⟨hh.2.1.trans hNL,hh.2.2.2.trans hNL⟩
  by_cases hl : Order.IsSuccLimit eta.1.repr
  · have hchild := mixed_limit_child q w v eta lower c d E F hR hS hq hl hlt
    refine ⟨?_,?_,?_⟩
    · intro x hx
      exact mixed_limit_sign_stable q w v eta lower c d E F hR hS hl hlt hchild hctx table hc N hDom
        x N (hNT.trans hx) hNT hx le_rfl
    · intro profile hp hWin
      exact mixed_high_gap q w v eta lower c d E F hR hS hl hlt hchild hctx table hc profile N hp hNT hDom hWin
    · intro profile hp hWin
      exact mixed_low_gap q w v eta lower c d E F hR hS hl hlt hchild hctx table hc profile N hNT hDom
        (hBounds profile hp).2 hWin
  · obtain ⟨added,last,hsource,hcode,hValid,hLow,hHigh,hStop,hValues⟩ :=
      mixed_normalized_source q w v eta lower c d E F hR hS hq hlt
    have hVals : ∀ x : Nat,N≤x →
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x=
          actualOneVariableComparisonValue (.range ((w++added)++[(last,c)]) E) x :=
      fun x hx => hValues x (hNL.trans hx)
    have hChild := mixed_normalized_child q w v added eta lower last c d E F hR hS hq hlt hsource hcode
    have hHighGap : ∀ profile∈[q.2.1,q.2.2],
        (∀ x : Nat,N≤x → actualOneVariableComparisonValue (.range (v++[(lower,d)]) F) x<
          actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x) →
        comparisonBareLimitGap (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F) profile N := by
      intro profile hp hWin
      exact gap_vacuous w eta c E hl _ profile N
    by_cases heq : last=lower
    · subst last
      simp only [if_true] at hChild
      have hMass := (mixed_mass_bound q w v eta lower c d E F hq _ hEta).trans hNL
      refine ⟨?_,hHighGap,?_⟩
      · intro x hx
        rw [hVals x hx,hVals N le_rfl]
        exact same_kernel_sign_stable q (w++added) v lower c d E F hValid hS hChild N hMass table hc
          x N (hNT.trans hx) hNT hx le_rfl
      · intro profile hp hWin
        apply gap_transfer_loser (.range (v++[(lower,d)]) F)
          (.range ((w++added)++[(lower,c)]) E) (.range (w++[(eta,c)]) E) profile N
          (fun x hx => (hVals x hx).symm)
        apply same_kernel_gap v (w++added) lower d c F E hS hValid profile N (hBounds profile hp).1
        intro x hx
        rw [←hVals x hx]
        exact hWin x hx
    · simp only [if_neg heq] at hChild
      have hLast : lower.1.repr<last.1.repr := by
        apply lt_of_le_of_ne hLow
        intro he
        apply heq
        apply Subtype.ext
        exact ONote.repr_inj.mp he.symm
      have hlLast : Order.IsSuccLimit last.1.repr := by
        rcases hStop with he | hh
        · exact (ne_of_gt hLast he).elim
        · exact hh
      refine ⟨?_,hHighGap,?_⟩
      · intro x hx
        rw [hVals x hx,hVals N le_rfl]
        exact mixed_limit_sign_stable q (w++added) v last lower c d E F hValid hS hlLast hLast hChild hctx
          table hc N hDom x N (hNT.trans hx) hNT hx le_rfl
      · intro profile hp hWin
        apply gap_transfer_loser (.range (v++[(lower,d)]) F)
          (.range ((w++added)++[(last,c)]) E) (.range (w++[(eta,c)]) E) profile N
          (fun x hx => (hVals x hx).symm)
        apply mixed_low_gap q (w++added) v last lower c d E F hValid hS hlLast hLast hChild hctx table hc
          profile N hNT hDom (hBounds profile hp).2
        intro x hx
        rw [←hVals x hx]
        exact hWin x hx

end LogicLineages.OrdinalComparison.RangeRangeNode
