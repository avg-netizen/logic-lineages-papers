module
public import LogicLineages.OrdinalComparison.SourceUnaryChainAlgebraProof
public import LogicLineages.OrdinalComparison.SourceUnaryChainSpineProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment

theorem partial_head_value {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (ws : List (OrdinalVector Γ 1)) : denote ν (partialSpine ws 1) = headSum ν ws := by
  induction ws with
  | nil => rfl
  | cons v ws ih =>
    change ordinalNaturalSum (ordinalNaturalSum (denote ν (v 1)) 1)
      (ordinalNaturalSum (ordinalNaturalSum 1 (denote ν (partialSpine ws 1))) 1) =
      ordinalNaturalSum (ordinalNaturalSum (denote ν (v 1)) 3) (headSum ν ws)
    rw [ih]
    exact head_step _ _

theorem fullSourceUnaryChain : Targets.FullSourceUnaryChain := by
  intro Γ vs
  obtain ⟨ws, hws⟩ := source_vectors vs
  obtain ⟨u, hu, _⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow .ground .ground)
    OrdinalSyntax.defaultPolicy (chainSource vs)
  refine ⟨ws, hws, u, hu, ?_⟩
  have hb := body_assignment vs ws hws
  have hu' := hu
  change (assignment OrdinalSyntax.defaultPolicy (chainBody vs)).bind
    (fun v => abstraction OrdinalSyntax.defaultPolicy v) = some u at hu'
  rw [hb] at hu'
  change abstraction OrdinalSyntax.defaultPolicy (fun _ : Fin 1 => spine ws) = some u at hu'
  have hh := abstraction_head (spine ws) (partialSpine ws) u (run_spine ws) hu'
  intro ν
  rw [hh]
  exact partial_head_value ν ws
end LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
