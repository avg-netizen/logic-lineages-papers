import LogicLineages.PersistentMarking.DecisionSourceSubstitutionSteps
namespace LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof DecisionSourceConstructProof

theorem preserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (q : Expr) (τ : Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : Typed Ξ q τ) (hu : Universe K V H Γ q)
    (hv : ArgsUniverse K V H Γ vs) : Universe K V H Γ (substitute vs d q) := by
  have go : ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
      Universe K V H Γ q → Universe K V H Γ (substitute vs d q) := by
    clear hc hu
    induction ht using Typed.rec
      (motive_2 := fun Ξ qs _ _ => ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
        ArgsUniverse K V H Γ qs → ArgsUniverse K V H Γ (substituteArgs vs d qs))
      (motive_3 := fun Ξ qs _ => ∀ (Ω : BoundContext) (d : Nat), SubCompatible vs d Ξ Ω →
        ArgsUniverse K V H Γ qs → ArgsUniverse K V H Γ (substituteArgs vs d qs)) with
    | free => intro Ω d hc hu; exact hu
    | bound hi => intro Ω d hc hu; exact boundLeaf K V H Γ vs d _ _ hu hv
    | lam ht ih =>
      intro Ω d hc hu
      exact lambdaStep K V H Γ _ Ω vs d _ _ _ hc ht hu
        (ih (Ω.push _) (d+1) (SpineSubstitutionProof.compatiblePush _ _ _ _ hc _) (lamChild _ _ _ _ _ _ hu))
    | head ht ih => intro Ω d hc hu; exact headStep K V H Γ _ _ vs d hu (ih Ω d hc (headBase _ _ _ _ _ _ hu))
    | marked hb he ihb ihe =>
      intro Ω d hc hu
      exact markedStep K V H Γ _ _ _ _ vs d hu
        (ihb Ω d hc (markedBase _ _ _ _ _ _ _ _ hu)) (ihe Ω d hc (markedExtras _ _ _ _ _ _ _ _ hu))
    | nil => trivial
    | cons hq hqs ihq ihqs =>
      rename_i Ω d hc hu
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
