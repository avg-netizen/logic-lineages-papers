module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSelectedCode
public import LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedCodeProof
open GorbowSyntax GorbowCodeConstructors GorbowSelectedCode

private theorem selectorValid (A : Selector) : GorbowSupportCode.selectorCode (GorbowFormulaPrefixCode.encode A.val) = true :=
  (GorbowSupportCodeProof.exactSelector _).mpr ⟨A,rfl⟩
private theorem sentenceValid (σ : Sentence) : GorbowSyntaxValidation.validFormula 0 (GorbowFormulaPrefixCode.encode σ) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 _ _).mpr ⟨σ,(GorbowFormulaPrefixCodeProof.decoderExact _ _ σ).mpr rfl⟩

theorem literalCalibration : Comparators.GorbowSelectedCode.LiteralCalibration := by
  intro A σ
  have hn := GorbowCodeConstructorsProof.numeralCalibration 1 (number (GorbowFormulaPrefixCode.encode σ))
  simp [everyoneRaw,everyoneSentence,everyone,GorbowFormulaPrefixCode.encode,GorbowTermPrefixCode.encode,
    binary,unary,variableCode,formulaNumber,hn]

private theorem everyoneEncoded (A : Selector) (σ : Sentence) :
    everyoneCode (GorbowFormulaPrefixCode.encode A.val) (GorbowFormulaPrefixCode.encode σ) =
      some (GorbowFormulaPrefixCode.encode (everyoneSentence A σ)) := by
  simp only [everyoneCode,selectorValid,sentenceValid,Bool.and_self,ite_true]
  exact congrArg some (literalCalibration A σ)

theorem exactEveryone : Comparators.GorbowSelectedCode.ExactEveryone := by
  intro a s out
  constructor
  · intro h
    unfold everyoneCode at h
    split at h
    · rename_i hg
      have hg' : GorbowSupportCode.selectorCode a = true ∧ GorbowSyntaxValidation.validFormula 0 s = true := by simpa using hg
      obtain ⟨A,rfl⟩ := (GorbowSupportCodeProof.exactSelector a).mp hg'.1
      obtain ⟨σ,hs⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 0 s).mp hg'.2
      have he := (GorbowFormulaPrefixCodeProof.decoderExact _ _ σ).mp hs
      subst s
      exact ⟨A,σ,rfl,rfl,(Option.some.inj h).symm.trans (literalCalibration A σ)⟩
    · simp at h
  · rintro ⟨A,σ,rfl,rfl,rfl⟩
    exact everyoneEncoded A σ

private theorem nonemptyEncoded (A : Selector) :
    nonemptyCode (GorbowFormulaPrefixCode.encode A.val) = some (GorbowFormulaPrefixCode.encode (selectedNonempty A)) := by
  simp [nonemptyCode,selectorValid,selectedNonempty,GorbowFormulaPrefixCode.encode,
    GorbowTermPrefixCode.encode,unary,binary,variableCode]

theorem exactNonempty : Comparators.GorbowSelectedCode.ExactNonempty := by
  intro a out
  constructor
  · intro h
    by_cases hg : GorbowSupportCode.selectorCode a = true
    · obtain ⟨A,rfl⟩ := (GorbowSupportCodeProof.exactSelector a).mp hg
      rw [nonemptyEncoded] at h
      exact ⟨A,rfl,(Option.some.inj h).symm⟩
    · simp [nonemptyCode,hg] at h
  · rintro ⟨A,rfl,rfl⟩
    exact nonemptyEncoded A

private theorem thetaEncoded (A : Selector) : thetaCode (GorbowFormulaPrefixCode.encode A.val) =
    some (GorbowFormulaPrefixCode.encode (theta A)) := by
  simp [thetaCode,everyoneEncoded,theta,GorbowFormulaPrefixCode.encode,binary]

theorem exactTheta : Comparators.GorbowSelectedCode.ExactTheta := by
  intro a out
  constructor
  · intro h
    by_cases hg : GorbowSupportCode.selectorCode a = true
    · obtain ⟨A,rfl⟩ := (GorbowSupportCodeProof.exactSelector a).mp hg
      rw [thetaEncoded] at h
      exact ⟨A,rfl,(Option.some.inj h).symm⟩
    · simp [thetaCode,everyoneCode,hg] at h
  · rintro ⟨A,rfl,rfl⟩
    exact thetaEncoded A

theorem realization : Comparators.GorbowSelectedCode.Realization := by
  intro I A σ
  refine ⟨everyone_realize I A (formulaNumber σ),selectedNonempty_realize I A,?_⟩
  change ((_ → falseEquality.realize I Fin.elim0) ↔ _)
  simp [falseEquality_not_realized I]

private theorem pr_unary {α : Type} [Primcodable α] (tag : Nat) {f : α → List Nat} (hf : Primrec f) :
    Primrec (fun x => unary tag (f x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const tag).pair hf)
private theorem pr_binary {α : Type} [Primcodable α] (tag : Nat) {f g : α → List Nat} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => binary tag (f x) (g x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp ((Primrec.const tag).pair (hf.pair hg))
private theorem pr_everyoneRaw : Primrec (fun p : List Nat × List Nat => everyoneRaw p.1 p.2) :=
  pr_unary 10 (pr_binary 7 (Primrec.const (unary 2 (variableCode 0)))
    (pr_binary 7 Primrec.fst (pr_binary 4 (Primrec.const (variableCode 0))
      (GorbowCodeConstructorsProof.uniformPrograms.2.2.2.1.comp
        (GorbowCodeConstructorsProof.uniformPrograms.2.2.2.2.comp Primrec.snd)))))
private theorem pr_everyoneCode : Primrec (fun p : List Nat × List Nat => everyoneCode p.1 p.2) := by
  have hg := Primrec.and.comp (GorbowSupportCodeProof.uniformPrograms.2.2.2.2.2.1.comp Primrec.fst)
    (GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2.comp ((Primrec.const 0).pair Primrec.snd))
  exact Primrec.ite (Primrec.eq.comp hg (Primrec.const true)) (Primrec.option_some.comp pr_everyoneRaw) (Primrec.const none)
private theorem pr_nonemptyCode : Primrec nonemptyCode :=
  Primrec.ite (Primrec.eq.comp GorbowSupportCodeProof.uniformPrograms.2.2.2.2.2.1 (Primrec.const true))
    (Primrec.option_some.comp (pr_unary 11 (pr_binary 8 (Primrec.const (unary 2 (variableCode 0))) Primrec.id))) (Primrec.const none)
private theorem pr_thetaCode : Primrec thetaCode := by
  have hs : Primrec (fun p : List Nat × List Nat => some (binary 7 p.2 (GorbowFormulaPrefixCode.encode falseEquality))) :=
    Primrec.option_some.comp (pr_binary 7 Primrec.snd (Primrec.const (GorbowFormulaPrefixCode.encode falseEquality)))
  exact Primrec.option_bind (pr_everyoneCode.comp (Primrec.id.pair (Primrec.const (GorbowFormulaPrefixCode.encode falseEquality)))) hs.to₂

theorem uniformPrograms : Comparators.GorbowSelectedCode.UniformPrograms :=
  ⟨pr_everyoneRaw,pr_everyoneCode,pr_nonemptyCode,pr_thetaCode⟩

theorem gorbowSelectedCode : Comparators.GorbowSelectedCode.Target :=
  ⟨literalCalibration,exactEveryone,exactNonempty,exactTheta,realization,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSelectedCodeProof
