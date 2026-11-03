module
public import LogicLineages.OrdinalComparison.OneUnitCodeSemanticProof
public import LogicLineages.OrdinalComparison.OneUnitCodePrimitiveProof
public import LogicLineages.OrdinalComparison.SourceOneUnitProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof

theorem actualCompilerTotality : Targets.ActualCompilerTotality := by
  intro Γ σ τ a
  obtain ⟨h,h',ps,ps',l,l',d,ha,hv,hl,hl',hp,hp',hc,hdd,hdd',hf,hd,hscalar,hgrowth,hsem⟩ :=
    OneUnit.Proof.actualHeadConstruction Γ σ τ a
  refine ⟨d,hc,?_,hd,?_⟩
  · rw [exactCompiler.2 Γ σ τ a,hc]
    rfl
  · intro hactive
    exact (hgrowth hactive).2.2
end LogicLineages.OrdinalComparison.Source.OneUnitCode.Proof
