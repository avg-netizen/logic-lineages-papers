import LogicLineages.PersistentMarking.DecisionSourceCallSupport
namespace LogicLineages.PersistentMarking.DecisionSourceCallProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof DecisionSourceConstructProof DecisionSourceSubstitutionProof DecisionSourceCallSupport

theorem auxiliary (K V H Γ) (types : List Ty) (vs : Args) (q : Expr) (σ : Ty) (args : Args) (r : Expr)
    (hk : Closed K) (hq : Typed (BoundContext.prefix types EmptyContext) q σ)
    (hv : BaseTyped EmptyContext vs types) (ha : ExtrasTyped EmptyContext args)
    (hu : Universe K V H Γ q) (hvu : ArgsUniverse K V H Γ vs) (hau : ArgsUniverse K V H Γ args)
    (hcall : applyAux q args vs = some r) : Universe K V H Γ r := by
  cases args with
  | nil =>
    simp only [applyAux,Option.some.injEq] at hcall; subst r
    exact boundSubstitution K V H Γ types vs q σ hq hv hu hvu
  | cons a rest =>
    cases ha with
    | cons hat hrest =>
      cases q with
      | free υ x => cases hcall
      | bound υ i => cases hcall
      | lam υ body =>
        cases hq with
        | lam hbody =>
          by_cases he : a.type = υ
          · simp only [applyAux,if_pos he] at hcall
            have hat' : Typed EmptyContext a υ := by
              have hh := SpineShiftProof.annotationExact _ _ _ hat
              simpa only [←hh,he] using hat
            exact auxiliary K V H Γ (υ::types) (.cons a vs) body _ rest r hk hbody (.cons hat' hv) hrest
              (lamChild _ _ _ _ _ _ hu) ⟨hau.1,hvu⟩ hau.2 hcall
          · simp [applyAux,he] at hcall
      | head f bs =>
        cases hq with
        | head hb =>
          cases hc : consumeTypes f.result (.cons a rest) with
          | none => simp [applyAux,hc] at hcall
          | some τ =>
            simp only [applyAux,hc,Option.map_some,Option.some.injEq] at hcall; subst r
            have ht : τ ∈ K := hk f.result (rootType K V H Γ (.head f bs) hu) τ (consumeSubtype f.result (.cons a rest) τ hc)
            exact markedBuild K V H Γ f τ _ _
              (fun υ hυ => hu.1 υ (List.mem_append_left _ hυ)) (fun υ hυ => hk τ ht υ hυ)
              (hu.2.1 f List.mem_cons_self)
              (basePreserves K V H Γ _ EmptyContext vs 0 bs _
                (SpineSubstitutionProof.finiteCompatible EmptyContext vs types hv) hb (headBase _ _ _ _ _ _ hu) hvu) hau
      | marked f υ bs es =>
        cases hq with
        | marked hb he =>
          cases hc : consumeTypes υ (.cons a rest) with
          | none => simp [applyAux,hc] at hcall
          | some τ =>
            simp only [applyAux,hc,Option.map_some,Option.some.injEq] at hcall; subst r
            have ht : τ ∈ K := hk υ (rootType K V H Γ (.marked f υ bs es) hu) τ (consumeSubtype υ (.cons a rest) τ hc)
            have compat := SpineSubstitutionProof.finiteCompatible EmptyContext vs types hv
            exact markedBuild K V H Γ f τ _ _
              (fun δ hδ => hu.1 δ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hδ))))
              (fun δ hδ => hk τ ht δ hδ) (hu.2.1 f List.mem_cons_self)
              (basePreserves K V H Γ _ EmptyContext vs 0 bs _ compat hb (markedBase _ _ _ _ _ _ _ _ hu) hvu)
              (appendUniverse K V H Γ _ _
                (extrasPreserves K V H Γ _ EmptyContext vs 0 es compat he (markedExtras _ _ _ _ _ _ _ _ hu) hvu) hau)
termination_by sizeOf args

theorem fullCall : DecisionSourceTargets.SourceFullCall := by
  intro K V H Γ q σ args τ r hk hq hargs hu hau hcall
  cases args with
  | nil => simp only [apply,Option.some.injEq] at hcall; subst r; exact hu
  | cons a rest => exact auxiliary K V H Γ [] .nil q σ (.cons a rest) r hk hq .nil
      (callExtras EmptyContext σ (.cons a rest) τ hargs) hu trivial hau hcall
end LogicLineages.PersistentMarking.DecisionSourceCallProof
