module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelfApplicationCode
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCodeProof
open GorbowSyntax GorbowSelfApplicationCode GorbowCodeConstructors

private theorem encodedSelf (φ : Formula 1) :
    selfApplicationCode (GorbowFormulaPrefixCode.encode φ) = some (GorbowFormulaPrefixCode.encode (selfInstance φ)) := by
  let σ : Fin 1 → Term 0 := fun _ => Term.numeral (formulaNumber φ)
  have hd : GorbowLiftedDictionary.dictionary σ = [numeral (formulaNumber φ)] := by
    simp [GorbowLiftedDictionary.dictionary,σ,List.ofFn_succ,
      GorbowCodeConstructorsProof.numeralCalibration 0 (formulaNumber φ)]
  have he : GorbowFormulaSubstitution.substituteFormula σ φ = selfInstance φ := by
    unfold selfInstance GorbowStandardInstances.instantiate
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  apply (GorbowSubstitutionCodeProof.exactOutput.2 1 0 _ _ _).mpr
  exact ⟨σ,φ,hd.symm,rfl,congrArg GorbowFormulaPrefixCode.encode he.symm⟩

theorem exactSelfApplication : Comparators.GorbowSelfApplicationCode.ExactSelfApplication := by
  intro raw out
  constructor
  · intro h
    obtain ⟨σ,φ,hd,hr,ho⟩ := (GorbowSubstitutionCodeProof.exactOutput.2 1 0 _ raw out).mp h
    subst raw
    rw [encodedSelf] at h
    exact ⟨φ,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨φ,rfl,rfl⟩
    exact encodedSelf φ

theorem exactRejection : Comparators.GorbowSelfApplicationCode.ExactRejection := by
  intro raw
  constructor
  · intro h
    cases hd : GorbowFormulaPrefixCode.decode 1 raw with
    | none => rfl
    | some φ =>
        have he := (GorbowFormulaPrefixCodeProof.decoderExact 1 raw φ).mp hd
        subst raw
        rw [encodedSelf] at h
        cases h
  · intro hd
    cases ho : selfApplicationCode raw with
    | none => rfl
    | some out =>
        obtain ⟨φ,hr,_⟩ := (exactSelfApplication raw out).mp ho
        have hdecode := (GorbowFormulaPrefixCodeProof.decoderExact 1 raw φ).mpr hr
        rw [hd] at hdecode
        cases hdecode

theorem exactSelectorApplication : Comparators.GorbowSelfApplicationCode.ExactSelectorApplication := by
  intro raw out
  constructor
  · intro h
    have hs : GorbowSupportCode.selectorCode raw = true := by
      by_contra hn
      simp [selectorSelfApplicationCode,hn] at h
    obtain ⟨A,hr⟩ := (GorbowSupportCodeProof.exactSelector raw).mp hs
    subst raw
    simp only [selectorSelfApplicationCode,hs,↓reduceIte,encodedSelf,Option.some.injEq] at h
    exact ⟨A,rfl,h.symm⟩
  · rintro ⟨A,rfl,rfl⟩
    have hs := (GorbowSupportCodeProof.exactSelector (GorbowFormulaPrefixCode.encode A.val)).mpr ⟨A,rfl⟩
    simp only [selectorSelfApplicationCode,hs,↓reduceIte,encodedSelf]

theorem standardSemantics : Comparators.GorbowSelfApplicationCode.StandardSemantics := by
  intro φ I
  exact GorbowStandardInstancesProof.numeralInstances 0 φ (formulaNumber φ) I Fin.elim0

private theorem pr_self : Primrec selfApplicationCode := by
  have hn := GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1.comp
    GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2
  have hd := Primrec.list_cons.comp hn (Primrec.const [])
  exact GorbowSubstitutionCodeProof.uniformPrograms.2.2.2.2.comp
    ((Primrec.const 1).pair ((Primrec.const 0).pair (hd.pair Primrec.id)))

private theorem pr_selectorSelf : Primrec selectorSelfApplicationCode :=
  Primrec.ite (Primrec.eq.comp GorbowSupportCodeProof.uniformPrograms.2.2.2.2.2.1 (Primrec.const true))
    pr_self (Primrec.const none)

theorem uniformPrograms : Comparators.GorbowSelfApplicationCode.UniformPrograms := ⟨pr_self,pr_selectorSelf⟩

theorem gorbowSelfApplicationCode : Comparators.GorbowSelfApplicationCode.Target :=
  ⟨exactSelfApplication,exactRejection,exactSelectorApplication,standardSemantics,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSelfApplicationCodeProof
