module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSelfApplication
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplicationProof
open GorbowSyntax GorbowSortedSyntaxCode GorbowSortedSelfApplication

private theorem encodedSelf (φ : Formula 1) :
    rawSelf (GorbowFormulaPrefixCode.encode φ)=some (GorbowFormulaPrefixCode.encode (selfInstance φ)) := by
  apply (GorbowInstanceCodeProof.exactInstance 0 _ _ _).mpr
  refine ⟨φ,Term.numeral (formulaCode φ),rfl,?_,rfl⟩
  exact (GorbowCodeConstructorsProof.numeralCalibration 0 (formulaCode φ)).symm

theorem rawExact : Comparators.GorbowSortedSelfApplication.RawExact := by
  intro raw out
  constructor
  · intro h
    obtain ⟨φ,t,hr,_,_⟩ := (GorbowInstanceCodeProof.exactInstance 0 raw _ out).mp h
    subst raw
    rw [encodedSelf] at h
    exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩; exact encodedSelf φ

theorem calibration : Comparators.GorbowSortedSelfApplication.Calibration := by
  intro φ
  have hd := GorbowSortedSyntaxCodeProof.actualCalibration.2.1 1 φ
  unfold selfApply
  rw [hd]
  change (rawSelf (GorbowFormulaPrefixCode.encode φ)).bind (fun out => some (formulaRawNumber out))=some (formulaCode (selfInstance φ))
  rw [encodedSelf]
  rfl

theorem numericExact : Comparators.GorbowSortedSelfApplication.NumericExact := by
  intro code out
  constructor
  · intro h
    cases hd : decodeFormulaRaw code with
    | none => simp [selfApply,hd] at h
    | some raw =>
      cases hs : rawSelf raw with
      | none => simp [selfApply,hd,hs] at h
      | some rawOut =>
        obtain ⟨φ,hr,ho⟩ := (rawExact raw rawOut).mp hs
        subst raw
        have hc : code=formulaCode φ := (GorbowSortedSyntaxCodeProof.exactRawDecoding.1 _ _).mp hd
        subst code
        rw [calibration] at h
        exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩; exact calibration φ

theorem rejection : Comparators.GorbowSortedSelfApplication.Rejection := by
  intro code
  constructor
  · intro h ⟨φ,hφ⟩
    subst code
    rw [calibration] at h
    cases h
  · intro h
    cases ho : selfApply code with
    | none => rfl
    | some out =>
      obtain ⟨φ,hφ,_⟩ := (numericExact code out).mp ho
      exact False.elim (h ⟨φ,hφ⟩)

private theorem pr_raw : Primrec rawSelf := by
  have hn := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1.comp
    GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1
  exact GorbowInstanceCodeProof.uniformPrograms.2.1.comp
    ((Primrec.const 0).pair (Primrec.id.pair hn))
private theorem pr_map : Primrec (fun raw : List Nat => (rawSelf raw).map formulaRawNumber) :=
  Primrec.option_map pr_raw (GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.1.comp Primrec.snd).to₂
private theorem pr_self : Primrec selfApply := by
  have h := Primrec.option_bind GorbowSortedSyntaxCodeProof.uniformPrograms.2.2.2.2.2.1
    (pr_map.comp Primrec.snd).to₂
  exact h.of_eq (fun code => by
    cases hd : decodeFormulaRaw code <;> simp [selfApply,hd]
    case some raw => cases rawSelf raw <;> rfl)

theorem uniformPrograms : Comparators.GorbowSortedSelfApplication.UniformPrograms := ⟨pr_raw,pr_self⟩
theorem gorbowSortedSelfApplication : Comparators.GorbowSortedSelfApplication.Target :=
  ⟨rawExact,numericExact,calibration,rejection,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedSelfApplicationProof
