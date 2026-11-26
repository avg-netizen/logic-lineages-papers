import LogicLineages.PersistentMarking.ProtectedSpineBoundInputProof
import LogicLineages.PersistentMarking.ProtectedSpineClosedImageProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.ProtectedSpineBoundVariableProof
open Spine FiniteDomainSchema HereditaryDomainCode ProtectedSpineEnvironment
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineAgreementTargets ProtectedSpineBoundTargets
open MarkedConstructorTargets (PrefixClosed)
open ProtectedSpineConstructorAgreementProof (lookup)

theorem variable (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (vs : Args) (removed kept : List Ty) (hc : PrefixClosed E)
    (hm : M ∈ MarkedFamilyCoherence.retained E H) (hv : BoundImages E H vs removed)
    (σ : Ty) (i : Nat) (ht : BoundContext.prefix kept (BoundContext.prefix removed EmptyContext) i = some σ) :
    Agreement E σ (evaluate S E H M (.bound σ i))
      (evaluate S E H M (substitute vs kept.length (.bound σ i)))
      (BoundSubstitutionInputs S E H M vs kept) (RetainedProtection kept) := by
  rw [ProtectedSpineBoundSyntaxProof.prefixAt] at ht
  by_cases hi : i < kept.length
  · have hk : kept[i]? = some σ := by simpa [hi] using ht
    have hs : substitute vs kept.length (.bound σ i) = .bound σ i := by simp [substitute,hi]
    rw [hs]
    exact lookup E σ (fun Γ a => boundCode E Γ a.bound σ i) (fun k => protectedLookup k i) _ _
      (fun Γ a b h => h.2.1 σ i hk) (fun _ _ h => congrArg (fun k => protectedLookup k i) h.1)
  · have hr : removed[i-kept.length]? = some σ := by
      simpa [hi,ProtectedSpineBoundSyntaxProof.emptyPrefix] using ht
    obtain ⟨v,hv',hTyped⟩ := ProtectedSpineBoundSyntaxProof.getTyped vs removed hv.1 (i-kept.length) σ hr
    have hcov := (ProtectedSpineBoundInputProof.getFacts E H vs
      (DecisionOccurrenceProof.baseExtras _ _ _ hv.1) hv.2 (i-kept.length) v hv').2
    have hs : substitute vs kept.length (.bound σ i) = v := by
      simp [substitute,hi,hv',ClosedSyntaxProof.closedShift v σ hTyped kept.length]
    rw [hs]
    have hvty := SpineShiftProof.annotationExact _ _ _ hTyped
    exact ProtectedSpineClosedImageProof.image S E H M v σ hc hm hTyped hcov
      (fun Γ a => boundCode E Γ a.bound σ i) (fun k => protectedLookup k i) _ _
      (by
        intro Γ a b h
        have h' := h.2.2 (i-kept.length) v hv'
        have he : kept.length+(i-kept.length) = i := by omega
        rw [hvty,he] at h'
        exact h')
      (by
        intro k l h
        have hk := h.2
        have hno : ¬i < k := by omega
        simp [protectedLookup,hno])

end LogicLineages.PersistentMarking.ProtectedSpineBoundVariableProof
