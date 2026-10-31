module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
open OriginalDomain

theorem fullSourceCollision : Targets.FullSourceCollision := by
  refine ⟨actualScalarTotal, actualGroundEraser, admissible_collision, ?_⟩
  intro Γ p q S ρ
  obtain ⟨ρ', he⟩ := originalSupportedExtension Γ S ρ
  have hv : valuation ρ' = supportedValuation ρ := funext he
  rw [← hv]
  exact admissible_collision Γ p q ρ'
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
