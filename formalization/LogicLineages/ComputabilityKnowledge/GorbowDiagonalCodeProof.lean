module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowDiagonalCode
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalSentenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplicationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowDiagonalCodeProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowDiagonalSentence GorbowDiagonalCode

private theorem encodedTheta (φ : Formula 1) :
    thetaRaw (GorbowFormulaPrefixCode.encode φ)=some (GorbowFormulaPrefixCode.encode (theta φ)) := by
  apply (GorbowSubstitutionCodeProof.exactOutput.2 1 1 _ _ _).mpr
  refine ⟨fun _ : Fin 1 => deltaTerm (.var 0),φ,?_,rfl,rfl⟩
  simp [GorbowLiftedDictionary.dictionary,List.ofFn_succ]

theorem rawExact : Comparators.GorbowDiagonalCode.RawExact := by
  intro raw out
  constructor
  · intro h
    obtain ⟨σ,φ,_,hr,_⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 1 1 _ raw out).mp h
    subst raw
    rw [encodedTheta] at h
    exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩; exact encodedTheta φ

theorem calibration : Comparators.GorbowDiagonalCode.Calibration := by
  intro φ
  unfold output
  rw [GorbowSortedSyntaxCodeProof.actualCalibration.2.1 1 φ]
  change (thetaRaw (GorbowFormulaPrefixCode.encode φ)).bind
    (fun body => GorbowSortedSelfApplication.selfApply (formulaRawNumber body))=_
  rw [encodedTheta]
  exact GorbowSortedSelfApplicationProof.calibration (theta φ)

theorem numericExact : Comparators.GorbowDiagonalCode.NumericExact := by
  intro code out
  constructor
  · intro h
    cases hd : decodeFormulaRaw code with
    | none => simp [output,hd] at h
    | some raw =>
      cases ht : thetaRaw raw with
      | none => simp [output,hd,ht] at h
      | some body =>
        obtain ⟨φ,hr,_⟩ := (rawExact raw body).mp ht
        subst raw
        have hc : code=formulaCode φ := (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 _ _).mp hd
        subst code
        rw [calibration] at h
        exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩; exact calibration φ

theorem rejection : Comparators.GorbowDiagonalCode.Rejection := by
  intro code
  constructor
  · intro h ⟨φ,hφ⟩
    subst code
    rw [calibration] at h
    cases h
  · intro h
    cases ho : output code with
    | none => rfl
    | some out =>
      obtain ⟨φ,hφ,_⟩ := (numericExact code out).mp ho
      exact False.elim (h ⟨φ,hφ⟩)

theorem provedOutput : Comparators.GorbowDiagonalCode.ProvedOutput := by
  intro φ out h
  rw [calibration] at h
  have he := Option.some.inj h
  subst out
  exact GorbowDiagonalSentenceProof.fixedPoint φ

private theorem pr_theta : Primrec thetaRaw :=
  GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const 1).pair ((Primrec.const 1).pair ((Primrec.const _).pair Primrec.id)))
private theorem pr_body : Primrec (fun raw : List Nat => (thetaRaw raw).bind
    (fun body => GorbowSortedSelfApplication.selfApply (formulaRawNumber body))) :=
  Primrec.option_bind pr_theta
    ((GorbowSortedSelfApplicationProof.uniformPrograms.2.comp
      GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1).comp Primrec.snd).to₂
private theorem pr_output : Primrec output := by
  have h := Primrec.option_bind GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1
    (pr_body.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by
    cases hd : decodeFormulaRaw code <;> simp [output,hd])

theorem uniformPrograms : Comparators.GorbowDiagonalCode.UniformPrograms := ⟨pr_theta,pr_output⟩
theorem gorbowDiagonalCode : Comparators.GorbowDiagonalCode.Target :=
  ⟨rawExact,numericExact,calibration,rejection,provedOutput,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowDiagonalCodeProof
