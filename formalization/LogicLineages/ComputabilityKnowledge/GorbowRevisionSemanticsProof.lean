module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionSemantics
public import LogicLineages.ComputabilityKnowledge.GorbowCodeConstructorsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPACoreProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRevisionSemanticsProof
open GorbowSyntax GorbowCodeConstructors GorbowPACore GorbowRevisionSemantics

theorem singletonCalibration : Comparators.GorbowRevisionSemantics.SingletonCalibration := by
  intro g P
  simp [interpretation,singletonKnowledge,singletonAccessible]

private theorem termFixed (g : Ground) (P Q : Extension) {n : Nat} (t : Term n) (v : Fin n → Nat) :
    t.realize (interpretation g P) v = t.realize (interpretation g Q) v := by
  induction t <;> simp_all [Term.realize,interpretation]
private theorem formulaFixed (g : Ground) (P Q : Extension) {n : Nat} (φ : Formula n) (v : Fin n → Nat)
    (hm : MinusFormula φ) : φ.realize (interpretation g P) v ↔ φ.realize (interpretation g Q) v := by
  induction φ <;> simp_all only [MinusFormula,Formula.realize,termFixed g P Q]
  all_goals rfl

theorem fixedMinus : Comparators.GorbowRevisionSemantics.FixedMinus := by
  intro g P Q
  exact ⟨fun _ t v => termFixed g P Q t v,fun _ φ v hm => formulaFixed g P Q φ v hm⟩

private theorem imageAt (g : Ground) (P : Extension) (σ : Sentence) :
    revise g P (formulaNumber σ) ↔ σ.realize (interpretation g P) Fin.elim0 := by
  constructor
  · rintro ⟨τ,he,ht⟩
    have hτσ : τ=σ := GorbowCodeConstructorsProof.numericInjection.2 0 he
    simpa [hτσ] using ht
  · intro h
    exact ⟨σ,rfl,h⟩

theorem exactImage : Comparators.GorbowRevisionSemantics.ExactImage := by
  intro g P
  refine ⟨imageAt g P,?_⟩
  intro c hn hr
  obtain ⟨σ,he,_⟩ := hr
  exact hn ⟨σ,he⟩

theorem successorCalibration : Comparators.GorbowRevisionSemantics.SuccessorCalibration := by
  intro g initial n σ
  simp only [truthSentence,allKnowledgeSentence,knowledgeSentence,Formula.realize,numeral_realize]
  change (revise g (extensions g initial n) (formulaNumber σ) ↔ _) ∧
    (revise g (extensions g initial n) (formulaNumber σ) ↔ _) ∧
    (∀ a, (a=0 ∧ revise g (extensions g initial n) (formulaNumber σ)) ↔ _)
  simp only [imageAt,stage]
  exact ⟨True.intro,True.intro,fun _ => True.intro⟩

theorem modelClauses : Comparators.GorbowRevisionSemantics.ModelClauses := by
  intro g P
  refine ⟨⟨0,rfl⟩,?_,?_⟩
  · intro c
    change P c ↔ ∀ a, a=0 → a=0 ∧ P c
    simp
  · intro a c _ h
    exact h.2

theorem positiveDistribution : Comparators.GorbowRevisionSemantics.PositiveDistribution := by
  intro g initial n σ τ hi hs
  change revise g (extensions g initial n) (formulaNumber τ)
  apply (imageAt g _ τ).mpr
  have hf := (imageAt g _ (.imp σ τ)).mp hi
  exact hf ((imageAt g _ σ).mp hs)

theorem coreSoundness : Comparators.GorbowRevisionSemantics.CoreSoundness := by
  intro g initial k n φ p v
  exact GorbowPACoreProof.proofSoundness n φ p (stage g initial k) v

theorem gorbowRevisionSemantics : Comparators.GorbowRevisionSemantics.Target :=
  ⟨singletonCalibration,fixedMinus,exactImage,successorCalibration,modelClauses,positiveDistribution,coreSoundness⟩
end LogicLineages.ComputabilityKnowledge.GorbowRevisionSemanticsProof
