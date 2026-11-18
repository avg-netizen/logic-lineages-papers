import LogicLineages.PersistentMarking.DecisionSourceSubstitutionSteps
namespace LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof DecisionSourceConstructProof

theorem preserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (q : Expr) (τ : Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : Typed Ξ q τ) (hu : Universe K V H Γ q)
    (hv : ArgsUniverse K V H Γ vs) : Universe K V H Γ (substitute vs d q) := by
  have go : ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
      Universe K V H Γ q → Universe K V H Γ (substitute vs d q) := by
    clear hc hu
    refine Typed.rec
      (motive_1 := fun Ξ q _ _ => ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
        Universe K V H Γ q → Universe K V H Γ (substitute vs d q))
      (motive_2 := fun Ξ qs _ _ => ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
        ArgsUniverse K V H Γ qs → ArgsUniverse K V H Γ (substituteArgs vs d qs))
      (motive_3 := fun Ξ qs _ => ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
        ArgsUniverse K V H Γ qs → ArgsUniverse K V H Γ (substituteArgs vs d qs))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ht
    · intro Ξ σ x Ω d hc hu; exact hu
    · intro Ξ i σ hi Ω d hc hu; exact boundLeaf K V H Γ vs d σ i hu hv
    · intro Ξ σ body τ ht ih Ω d hc hu
      exact lambdaStep K V H Γ Ξ Ω vs d σ body τ hc ht hu
        (ih (Ω.push σ) (d+1) (SpineSubstitutionProof.compatiblePush _ _ _ _ hc σ) (lamChild _ _ _ _ _ _ hu))
    · intro Ξ bs f ht ih Ω d hc hu
      exact headStep K V H Γ f bs vs d hu (ih Ω d hc (headBase _ _ _ _ _ _ hu))
    · intro Ξ bs f es τ hb he ihb ihe Ω d hc hu
      exact markedStep K V H Γ f τ bs es vs d hu
        (ihb Ω d hc (markedBase _ _ _ _ _ _ _ _ hu)) (ihe Ω d hc (markedExtras _ _ _ _ _ _ _ _ hu))
    · intros; trivial
    · intro Ξ q σ qs types hq hqs ihq ihqs Ω d hc hu
      exact ⟨ihq Ω d hc hu.1,ihqs Ω d hc hu.2⟩
    · intros; trivial
    · intro Ξ q σ qs hq hqs ihq ihqs Ω d hc hu
      exact ⟨ihq Ω d hc hu.1,ihqs Ω d hc hu.2⟩
  exact go Ω d hc hu

theorem basePreserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (qs : Args) (types : List Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : BaseTyped Ξ qs types) (hu : ArgsUniverse K V H Γ qs)
    (hv : ArgsUniverse K V H Γ vs) : ArgsUniverse K V H Γ (substituteArgs vs d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => cases ht with
    | cons hq hqs => exact ⟨preserves K V H Γ Ξ Ω vs d q _ hc hq hu.1 hv,basePreserves K V H Γ Ξ Ω vs d qs _ hc hqs hu.2 hv⟩
termination_by sizeOf qs

theorem extrasPreserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (qs : Args)
    (hc : SubCompatible vs d Ξ Ω) (ht : ExtrasTyped Ξ qs) (hu : ArgsUniverse K V H Γ qs)
    (hv : ArgsUniverse K V H Γ vs) : ArgsUniverse K V H Γ (substituteArgs vs d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => cases ht with
    | cons hq hqs => exact ⟨preserves K V H Γ Ξ Ω vs d q _ hc hq hu.1 hv,extrasPreserves K V H Γ Ξ Ω vs d qs hc hqs hu.2 hv⟩
termination_by sizeOf qs

theorem boundSubstitution : DecisionSourceTargets.SourceBoundSubstitution := by
  intro K V H Γ types vs q τ hq hv hu hvs
  exact preserves K V H Γ (BoundContext.prefix types EmptyContext) EmptyContext vs 0 q τ
    (SpineSubstitutionProof.finiteCompatible EmptyContext vs types hv) hq hu hvs
end LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
