module
public import LogicLineages.OrdinalComparison.SourceTypedCodeAdequacyInjectivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof

theorem genericControlTransport : Targets.GenericControlTransport := by
  constructor
  · intro Γ τ t u h
    have ht := typedCodeInjective Γ τ h
    cases ht
    rfl
  · intro G Γ t u h
    have ht := typedCodeInjective Γ .ground h
    cases ht
    exact ⟨fun _ _ => Iff.rfl,fun _ _ => Iff.rfl⟩
end LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof
