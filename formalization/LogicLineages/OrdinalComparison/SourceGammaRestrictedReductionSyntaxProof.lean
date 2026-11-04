module
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionTargets
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionAdequacyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Proof

theorem canonical (n : Nat) (left right : OriginalTerm (List.replicate n Ty.ground) .ground) :
    RestrictedSyntax (SourceMachineQueryCode.pack (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) ↔
    SourceGroundBinderFragment.Fragment left ∧ SourceGroundBinderFragment.Fragment right ∧
    SourceClasses.InternalLevelBound 1 left ∧ SourceClasses.InternalLevelBound 1 right := by
  constructor
  · rintro ⟨m,a,b,hd,hs⟩
    rw [SourceMachineQueryCode.Proof.roundtrip] at hd
    have he := Option.some.inj hd
    have hn : n=m := congrArg Prod.fst he
    subst m
    have hl := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.1) he)
    have hr := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.2) he)
    cases hl
    cases hr
    exact hs
  · intro h
    exact ⟨n,left,right,SourceMachineQueryCode.Proof.roundtrip _,h⟩

theorem exactSyntaxClass : Targets.ExactSyntaxClass := by
  intro Γ hg left right
  have hc := SourceGammaCodedReduction.Proof.ground_context Γ hg
  generalize hn : Γ.length=n at hc
  subst Γ
  simpa only [List.length_replicate] using canonical n left right
end LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Proof
