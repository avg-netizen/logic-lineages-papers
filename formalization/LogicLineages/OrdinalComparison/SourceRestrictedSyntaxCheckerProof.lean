module
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerFragmentProof
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerProgramsProof
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof

theorem ground_iff (n c : Nat) : groundCode n c=true ↔
    ∃ t : OriginalTerm (List.replicate n Ty.ground) .ground, SyntaxCode.encodeTerm t=c := by
  simp only [groundCode,decide_eq_true_eq]
  have h := SyntaxCode.Proof.typedCheckExact (List.replicate n Ty.ground) Ty.ground c
  simpa only [List.map_replicate] using h

theorem all_ground (n : Nat) : SourceMachineRawValuations.AllGround (List.replicate n Ty.ground) := by
  intro σ hσ
  exact (List.mem_replicate.mp hσ).2

theorem exactSyntaxClass : Targets.ExactSyntaxClass := by
  intro c
  cases hc : SourceMachineQueryCode.unpack c with
  | none =>
    simp only [restrictedCode,hc,Bool.false_eq_true,false_iff]
    rintro ⟨n,l,r,he,_⟩
    rw [hc] at he
    cases he
  | some q =>
    rcases q with ⟨n,l,r⟩
    simp only [restrictedCode,hc,Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨hl,hr⟩,hfl⟩,hfr⟩
      obtain ⟨left,hel⟩ := (ground_iff n l).mp hl
      obtain ⟨right,her⟩ := (ground_iff n r).mp hr
      subst l
      subst r
      have hleft := (fragmentCalibration _ _ left).mp hfl
      have hright := (fragmentCalibration _ _ right).mp hfr
      exact ⟨n,left,right,hc,hleft,hright,
        SourceMachineInternalLevel.Proof.structuralLevel _ _ left (all_ground n) hleft,
        SourceMachineInternalLevel.Proof.structuralLevel _ _ right (all_ground n) hright⟩
    · rintro ⟨m,left,right,he,hleft,hright,_,_⟩
      have heq := Option.some.inj (hc.symm.trans he)
      cases heq
      exact ⟨⟨⟨(ground_iff _ _).mpr ⟨left,rfl⟩,(ground_iff _ _).mpr ⟨right,rfl⟩⟩,
        (fragmentCalibration _ _ left).mpr hleft⟩,(fragmentCalibration _ _ right).mpr hright⟩
end LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof
