module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeSemanticProof
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodePrimitiveProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof

theorem actualAnchorCalibration : Targets.ActualAnchorCalibration := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro Γ hΓ τ t
  obtain ⟨w,s,hw,hs,hcode,hclosed,hopen,hpos,hvalue⟩ :=
    AbsoluteObserver.Proof.anchorCorrect Γ hΓ τ t
  change AbsoluteObserver.openSourceValue (Γ.length,SyntaxCode.encodeTerm t) = _ ∧
    0 < AbsoluteObserver.openSourceValue (Γ.length,SyntaxCode.encodeTerm t)
  exact ⟨hopen,hopen.symm ▸ hpos⟩
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Proof
