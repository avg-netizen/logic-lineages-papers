module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationBridgeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitElimination.Proof

theorem build_total_sound (fuel : Nat) :
    ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ), Γ.length<fuel →
      ∃ q : Tree (Nat×Nat) Γ, build fuel t=some q ∧
        ∀ (ρ : Variable Γ .ground → Nat) (r : Nat), Eval (realize q) ρ r ↔ RawGraph t ρ r := by
  induction fuel with
  | zero => intro Γ τ t h; omega
  | succ fuel ih =>
    intro Γ τ t hlen
    cases hsel : select Γ with
    | ground hΓ =>
      refine ⟨.leaf (groundBlock hΓ t),?_,fun ρ r => ground_leaf hΓ t ρ r⟩
      simp only [build,hsel,step]
    | found left right σ hσ =>
      obtain ⟨d,hd,hgraph⟩ := one_unit_graph left right σ τ hσ t
      have hchild : (left++right).length<fuel := by
        simp only [List.length_append,List.length_cons] at hlen ⊢
        omega
      obtain ⟨q,hq,hsq⟩ := ih (left++right) _
        (OneUnit.first (t.rename (SelectedBinder.moveToHead left right σ))) hchild
      cases hf : d.free with
      | true =>
        refine ⟨.free left right σ d.d q,?_,?_⟩
        · simp only [build,hsel,step,hd,hf,↓reduceIte,hq,Bind.bind,Pure.pure,Option.bind_some]
        · intro ρ r
          exact (free_node left right σ τ _ d hf q hsq ρ r).trans (hgraph ρ r)
      | false =>
        obtain ⟨s,hs,hss⟩ := ih (left++right) _
          (OneUnit.second (t.rename (SelectedBinder.moveToHead left right σ))) hchild
        refine ⟨.active left right σ (OneUnit.coefficient τ) d.d d.d' (OneUnit.constant τ d) q s,?_,?_⟩
        · simp only [build,hsel,step,hd,hf,Bool.false_eq_true,↓reduceIte,hq,hs,Bind.bind,Pure.pure,Option.bind_some]
        · intro ρ r
          exact (active_node left right σ τ _ d hf q s hsq hss ρ r).trans (hgraph ρ r)

theorem fullSourceUnitElimination : Targets.FullSourceUnitElimination := by
  refine ⟨program_values_computable,realize_anchors,?_⟩
  intro Γ τ t
  obtain ⟨q,hq,he⟩ := build_total_sound (Γ.length+1) Γ τ t (Nat.lt_succ_self _)
  exact ⟨q,hq,all_sources_ground (realize q),he⟩
end LogicLineages.OrdinalComparison.Source.UnitElimination.Proof
