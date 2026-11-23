module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationBoundProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationSubstitutionProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowPreservationGuardProof NumberedWindowPreservationBoundProof
open NumberedWindowNumberedDomainProof (ArgsGuard)
open NumberedWindowApplicationDomainProof (rootInWindow)

mutual
theorem term (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (values : NArgs) (d : Nat) (C D : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (h : InWindow S K C τ q) (hc : Compatible S K values d C D) :
    InWindow S K D τ (substitute values d q) := by
  have ht := h.1
  cases ht with
  | free => exact ⟨.free,h.2⟩
  | bound hi => exact hc _ _ hi (rootInWindow h)
  | bottom => exact ⟨.bottom,h.2⟩
  | lam hb =>
    exact NumberedWindowPreservationGuardProof.lam (hk _ (rootInWindow h))
      (term S K hk values (d+1) _ _ _ _ (lamBody h) (push hk hc))
  | ordinary hb =>
    obtain ⟨_,hf,hbs⟩ := ordinaryParts h
    obtain ⟨hb',hs⟩ := base S K hk values d C D _ _ hb hbs hc
    exact ordinary hb' hf hs
  | numbered hb he =>
    obtain ⟨_,_,hf,hbs,hes⟩ := NumberedWindowNumberedDomainProof.parts h
    obtain ⟨hb',hs⟩ := base S K hk values d C D _ _ hb hbs hc
    obtain ⟨he',ht'⟩ := extras S K hk values d C D _ he hes hc
    exact NumberedWindowNumberedDomainProof.numbered hb' he' hf
      (hk _ (rootInWindow h)) hs ht'
  | auxApp hq ha =>
    have parts := appParts h
    exact NumberedWindowApplicationDomainProof.app S K D _ _ _ _ hk
      (term S K hk values d C D _ _ parts.1 hc)
      (term S K hk values d C D _ _ parts.2 hc)
termination_by sizeOf q

theorem base (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (values : NArgs) (d : Nat) (C D : Spine.BoundContext) (qs : NArgs) (types : List Ty)
    (h : BaseTyped C qs types) (hg : ArgsGuard S K qs) (hc : Compatible S K values d C D) :
    BaseTyped D (substituteArgs values d qs) types ∧ ArgsGuard S K (substituteArgs values d qs) := by
  cases h with
  | nil => exact ⟨.nil,nilGuard⟩
  | cons hq hs =>
    have parts := consParts hg
    have hq' := term S K hk values d C D _ _ ⟨hq,parts.1⟩ hc
    have hs' := base S K hk values d C D _ _ hs parts.2 hc
    exact ⟨.cons hq'.1 hs'.1,consGuard hq'.2 hs'.2⟩
termination_by sizeOf qs

theorem extras (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (values : NArgs) (d : Nat) (C D : Spine.BoundContext) (qs : NArgs)
    (h : ExtrasTyped C qs) (hg : ArgsGuard S K qs) (hc : Compatible S K values d C D) :
    ExtrasTyped D (substituteArgs values d qs) ∧ ArgsGuard S K (substituteArgs values d qs) := by
  cases h with
  | nil => exact ⟨.nil,nilGuard⟩
  | cons hq hs =>
    have parts := consParts hg
    have hq' := term S K hk values d C D _ _ ⟨hq,parts.1⟩ hc
    have hs' := extras S K hk values d C D _ hs parts.2 hc
    exact ⟨.cons hq'.1 hs'.1,consGuard hq'.2 hs'.2⟩
termination_by sizeOf qs
end

theorem beta {S K C σ τ q a} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C τ (.auxApp σ τ (.lam σ q) a)) :
    InWindow S K C τ (substitute (.cons a .nil) 0 q) := by
  have parts := appParts h
  exact term S K hk _ 0 _ _ _ _ (lamBody parts.1) (one hk parts.2)

end LogicLineages.PersistentMarking.NumberedWindowPreservationSubstitutionProof
