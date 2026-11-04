module
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionTargets
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourceTypedCodeAdequacyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof

theorem ground_context (Γ : List Ty) (h : SourceMachineRawValuations.AllGround Γ) :
    Γ=List.replicate Γ.length Ty.ground := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hs := h σ (List.mem_cons_self)
    have ht : SourceMachineRawValuations.AllGround Γ := fun τ hm => h τ (List.mem_cons_of_mem _ hm)
    calc
      σ::Γ = Ty.ground::Γ := congrArg (fun τ => τ::Γ) hs
      _ = Ty.ground::List.replicate Γ.length Ty.ground := congrArg (List.cons Ty.ground) (ih ht)
      _ = List.replicate (σ::Γ).length Ty.ground := rfl

theorem canonical (G : Nat → Nat) (n : Nat)
    (left right : OriginalTerm (List.replicate n Ty.ground) .ground) :
    Member G (SourceMachineQueryCode.pack (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) ↔ Strict G left right := by
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

theorem canonicalQueryAdequacy : Targets.CanonicalQueryAdequacy := by
  intro G Γ hg left right
  have hc := ground_context Γ hg
  generalize hn : Γ.length=n at hc
  subst Γ
  simpa only [List.length_replicate] using canonical G n left right
end LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof
