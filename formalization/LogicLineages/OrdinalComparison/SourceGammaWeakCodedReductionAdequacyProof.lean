module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionTargets
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionAdequacyProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof

theorem canonical (G : Nat → Nat) (n : Nat)
    (left right : OriginalTerm (List.replicate n Ty.ground) .ground) :
    RawMember G (SourceMachineQueryCode.pack
      (n, SyntaxCode.encodeTerm left, SyntaxCode.encodeTerm right)) ↔ Weak G left right := by
  constructor
  · rintro ⟨m, a, b, hd, hs⟩
    rw [SourceMachineQueryCode.Proof.roundtrip] at hd
    have he := Option.some.inj hd
    have hn : n = m := congrArg Prod.fst he
    subst m
    have hl := SourceTypedCodeAdequacy.Proof.typedCodeInjective
      (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.1) he)
    have hr := SourceTypedCodeAdequacy.Proof.typedCodeInjective
      (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.2) he)
    cases hl
    cases hr
    exact hs
  · intro h
    exact ⟨n, left, right, SourceMachineQueryCode.Proof.roundtrip _, h⟩

theorem canonicalAdequacy : Targets.CanonicalAdequacy := by
  intro G Γ hg left right
  have hc := SourceGammaCodedReduction.Proof.ground_context Γ hg
  generalize hn : Γ.length = n at hc
  subst Γ
  simpa only [List.length_replicate] using canonical G n left right

end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof
