module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRevisionComposition
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemanticsProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstancesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRevisionCompositionProof
open GorbowSyntax GorbowStandardInstances GorbowRevisionSemantics GorbowRevisionComposition

private theorem truthNext (g : Ground) (initial : Extension) (n : Nat) (σ : Sentence) :
    (truthSentence σ).realize (stage g initial (n+1)) Fin.elim0 ↔ σ.realize (stage g initial n) Fin.elim0 :=
  (GorbowRevisionSemanticsProof.successorCalibration g initial n σ).1

theorem booleanTruth : Comparators.GorbowRevisionComposition.BooleanTruth := by
  intro g initial n σ τ
  simp [truthNext,Formula.realize]

theorem fullTermQuantifiers : Comparators.GorbowRevisionComposition.FullTermQuantifiers := by
  intro g initial n A
  simp only [truthNext]
  constructor
  · constructor
    · intro h t
      exact (GorbowStandardInstancesProof.literalInstantiation 0 A.val t (stage g initial n) Fin.elim0).mpr
        (h (t.realize (stage g initial n) Fin.elim0))
    · intro h x
      exact (GorbowStandardInstancesProof.numeralInstances 0 A.val x (stage g initial n) Fin.elim0).mp
        (h (Term.numeral x))
  · constructor
    · rintro ⟨x,hx⟩
      exact ⟨Term.numeral x,(GorbowStandardInstancesProof.numeralInstances 0 A.val x (stage g initial n) Fin.elim0).mpr hx⟩
    · rintro ⟨t,ht⟩
      exact ⟨t.realize (stage g initial n) Fin.elim0,
        (GorbowStandardInstancesProof.literalInstantiation 0 A.val t (stage g initial n) Fin.elim0).mp ht⟩

private theorem atomicMinus {k : Nat} {R : Formula k} (h : AtomicMinus R) : MinusFormula R := by
  cases R <;> simp_all [AtomicMinus,MinusFormula]

theorem atomicTruth : Comparators.GorbowRevisionComposition.AtomicTruth := by
  intro g initial n k R hr _ σ _
  rw [truthNext]
  have hv : (fun i => (σ i).realize (stage g initial n) Fin.elim0) =
      (fun i => (σ i).realize (stage g initial (n+1)) Fin.elim0) := by
    funext i
    exact (GorbowRevisionSemanticsProof.fixedMinus g (extensions g initial n) (extensions g initial (n+1))).1 0 (σ i) Fin.elim0
  have hm := (GorbowRevisionSemanticsProof.fixedMinus g (extensions g initial n) (extensions g initial (n+1))).2
    k R (fun i => (σ i).realize (stage g initial n) Fin.elim0) (atomicMinus hr)
  have hs := GorbowFormulaSubstitution.substituteFormula_realize R (stage g initial n) Fin.elim0 σ
  exact hs.trans (hm.trans (by rw [hv]; rfl))

theorem arithmeticBarcan : Comparators.GorbowRevisionComposition.ArithmeticBarcan := by
  intro g initial n A a ha h
  have ha0 : a=0 := ha
  apply (GorbowRevisionSemanticsProof.successorCalibration g initial n (.all A.val)).2.2 a |>.mpr
  refine ⟨ha0,?_⟩
  intro x
  have hx := h (Term.numeral x) (GorbowStandardInstancesProof.arithmeticNumerals 0 x)
  have hi := ((GorbowRevisionSemanticsProof.successorCalibration g initial n (instantiate A.val (Term.numeral x))).2.2 a).mp hx
  exact (GorbowStandardInstancesProof.numeralInstances 0 A.val x (stage g initial n) Fin.elim0).mp hi.2

theorem gorbowRevisionComposition : Comparators.GorbowRevisionComposition.Target :=
  ⟨booleanTruth,fullTermQuantifiers,atomicTruth,arithmeticBarcan⟩
end LogicLineages.ComputabilityKnowledge.GorbowRevisionCompositionProof
