module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowBooleanTruth
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowBooleanTruthProof
open GorbowSyntax GorbowBooleanTruth GorbowRegistryTuple GorbowRevisionSemantics GorbowCodeConstructors

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as

theorem guardCalibration : Comparators.GorbowBooleanTruth.GuardCalibration := by
  intro n t P ρ
  change GorbowBooleanRegistry.relationProgram ((headerTerm 1 0 [t]).realize (interpretation GorbowBooleanRegistry.ground P) ρ)=true ↔ _
  rw [headerRealize,GorbowBooleanRegistryProof.exactRelation]
  simp only [List.map_cons,List.map_nil]
  constructor
  · rintro ⟨σ,hσ⟩
    have he := (GorbowRegistryTupleProof.headerInjection _ _ _ _ _ _).mp hσ
    exact ⟨σ,by simpa using he.2.2⟩
  · rintro ⟨σ,hσ⟩
    exact ⟨σ,by rw [hσ]⟩

private theorem negRealize {n : Nat} (s : Term n) P ρ :
    (negCodeTerm s).realize (interpretation GorbowBooleanRegistry.ground P) ρ =
      GorbowBooleanRegistry.functionProgram (header 1 0 [s.realize (interpretation GorbowBooleanRegistry.ground P) ρ]) := by
  change GorbowBooleanRegistry.functionProgram ((headerTerm 1 0 [s]).realize _ ρ)=_
  rw [headerRealize]
  rfl
private theorem binaryRealize {n : Nat} (tag : Nat) (s t : Term n) P ρ :
    (binaryCodeTerm tag s t).realize (interpretation GorbowBooleanRegistry.ground P) ρ =
      GorbowBooleanRegistry.functionProgram (header 2 tag [s.realize (interpretation GorbowBooleanRegistry.ground P) ρ,t.realize (interpretation GorbowBooleanRegistry.ground P) ρ]) := by
  change GorbowBooleanRegistry.functionProgram ((headerTerm 2 tag [s,t]).realize _ ρ)=_
  rw [headerRealize]
  rfl

theorem functionCalibration : Comparators.GorbowBooleanTruth.FunctionCalibration := by
  intro n s t P ρ σ τ hs ht
  simp only [negRealize,binaryRealize,hs,ht]
  exact GorbowBooleanRegistryProof.functionCalibration σ τ

private theorem truthCodes (initial : Extension) (k : Nat) (σ τ : Sentence) :
    (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber (.neg σ)) ↔
      ¬ extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber σ)) ∧
    (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber (.imp σ τ)) ↔
      (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber σ) → extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber τ))) ∧
    (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber (.conj σ τ)) ↔
      (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber σ) ∧ extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber τ))) ∧
    (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber (.disj σ τ)) ↔
      (extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber σ) ∨ extensions GorbowBooleanRegistry.ground initial (k+1) (formulaNumber τ))) := by
  simpa [truthSentence,Formula.realize,numeral_realize,stage,interpretation] using
    GorbowRevisionCompositionProof.booleanTruth GorbowBooleanRegistry.ground initial k σ τ

private theorem instances (initial : Extension) (k n : Nat) (s t : Term n) ρ
    (hs : (sentenceGuard s).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ)
    (ht : (sentenceGuard t).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ) :
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize (stage GorbowBooleanRegistry.ground initial (k+1)) ρ := by
  obtain ⟨σ,hσ⟩ := (guardCalibration n s _ ρ).mp hs
  obtain ⟨τ,hτ⟩ := (guardCalibration n t _ ρ).mp ht
  obtain ⟨hn,hi,hc,hd⟩ := functionCalibration n s t _ ρ σ τ hσ hτ
  have hh := truthCodes initial k σ τ
  simp only [stage,interpretation] at hn hi hc hd hσ hτ
  simpa only [biconditional,Formula.realize,hn,hi,hc,hd,hσ,hτ,stage,interpretation,iff_def] using hh

attribute [local irreducible] headerTerm pairTerm tupleTerm

private theorem closeBoolean (I : Interpretation)
    (h : ∀ (n : Nat) (s t : Term n) ρ,
      (sentenceGuard s).realize I ρ → (sentenceGuard t).realize I ρ →
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize I ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize I ρ) :
    negAxiom.realize I Fin.elim0 ∧ impAxiom.realize I Fin.elim0 ∧
    conjAxiom.realize I Fin.elim0 ∧ disjAxiom.realize I Fin.elim0 := by
  constructor
  · intro x hx
    exact (h 1 (.var 0) (.var 0) (Fin.cases x Fin.elim0) hx hx).1
  constructor
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.1
  constructor
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.2.1
  · intro x y hxy
    exact (h 2 (.var 1) (.var 0) (Fin.cases y (Fin.cases x Fin.elim0)) hxy.1 hxy.2).2.2.2

theorem positiveBooleanAxioms : Comparators.GorbowBooleanTruth.PositiveBooleanAxioms :=
  fun initial k => closeBoolean _ (instances initial k)

theorem gorbowBooleanTruth : Comparators.GorbowBooleanTruth.Target :=
  ⟨guardCalibration,functionCalibration,positiveBooleanAxioms⟩
end LogicLineages.ComputabilityKnowledge.GorbowBooleanTruthProof
