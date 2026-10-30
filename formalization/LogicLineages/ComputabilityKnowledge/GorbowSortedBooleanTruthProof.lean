module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedBooleanTruth
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruthProof
open GorbowSyntax GorbowBooleanTruth GorbowRegistryTuple GorbowSortedRevision GorbowSortedSyntaxCode

private theorem headerRealize {n : Nat} (arity tag : Nat) (as : List (Term n)) I ρ :
    (headerTerm arity tag as).realize I ρ=header arity tag (as.map (fun t => t.realize I ρ)) :=
  (GorbowRegistryTupleProof.termCalibration n I ρ).2.2 arity tag as

theorem guardCalibration : Comparators.GorbowSortedBooleanTruth.GuardCalibration := by
  intro n t P ρ
  change GorbowSortedRegistry.relationProgram ((headerTerm 1 0 [t]).realize (interpretation GorbowSortedRegistry.ground P) ρ)=true ↔ _
  rw [headerRealize]
  simp only [List.map_cons,List.map_nil]
  rw [(GorbowSortedRegistryProof.relationDispatch (t.realize (interpretation GorbowSortedRegistry.ground P) ρ) 0).1]
  exact GorbowSortedBooleanCodeProof.exactDomains.1 _

private theorem negRealize {n : Nat} (s : Term n) P ρ :
    (negCodeTerm s).realize (interpretation GorbowSortedRegistry.ground P) ρ =
      GorbowSortedRegistry.functionProgram (header 1 0 [s.realize (interpretation GorbowSortedRegistry.ground P) ρ]) := by
  change GorbowSortedRegistry.functionProgram ((headerTerm 1 0 [s]).realize _ ρ)=_
  rw [headerRealize]
  rfl
private theorem binaryRealize {n : Nat} (tag : Nat) (s t : Term n) P ρ :
    (binaryCodeTerm tag s t).realize (interpretation GorbowSortedRegistry.ground P) ρ =
      GorbowSortedRegistry.functionProgram (header 2 tag [s.realize (interpretation GorbowSortedRegistry.ground P) ρ,t.realize (interpretation GorbowSortedRegistry.ground P) ρ]) := by
  change GorbowSortedRegistry.functionProgram ((headerTerm 2 tag [s,t]).realize _ ρ)=_
  rw [headerRealize]
  rfl

theorem functionCalibration : Comparators.GorbowSortedBooleanTruth.FunctionCalibration := by
  intro n s t P ρ σ τ hs ht
  simp only [negRealize,binaryRealize,hs,ht]
  obtain ⟨hn,hi,hc,hd,ha,hx,hinst⟩ := GorbowSortedRegistryProof.functionDispatch (formulaCode σ) (formulaCode τ) 0
  rw [hn,hi,hc,hd]
  exact GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ

private theorem truthCodes (initial : Extension) (k : Nat) (σ τ : Sentence) :
    (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode (.neg σ)) ↔
      ¬ extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode σ)) ∧
    (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode (.imp σ τ)) ↔
      (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode σ) → extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode τ))) ∧
    (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode (.conj σ τ)) ↔
      (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode σ) ∧ extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode τ))) ∧
    (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode (.disj σ τ)) ↔
      (extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode σ) ∨ extensions GorbowSortedRegistry.ground initial (k+1) (formulaCode τ))) := by
  simpa [truthSentence,formulaQuote,Formula.realize,numeral_realize,stage,interpretation,GorbowRevisionSemantics.interpretation] using
    GorbowSortedRevisionCompositionProof.booleanTruth GorbowSortedRegistry.ground initial k σ τ

private theorem instances (initial : Extension) (k n : Nat) (s t : Term n) ρ
    (hs : (sentenceGuard s).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ)
    (ht : (sentenceGuard t).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ) :
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize (stage GorbowSortedRegistry.ground initial (k+1)) ρ := by
  obtain ⟨σ,hσ⟩ := (guardCalibration n s _ ρ).mp hs
  obtain ⟨τ,hτ⟩ := (guardCalibration n t _ ρ).mp ht
  obtain ⟨hn,hi,hc,hd⟩ := functionCalibration n s t _ ρ σ τ hσ hτ
  have hh := truthCodes initial k σ τ
  simp only [stage,interpretation,GorbowRevisionSemantics.interpretation] at hn hi hc hd hσ hτ
  simpa only [biconditional,Formula.realize,hn,hi,hc,hd,hσ,hτ,stage,interpretation,GorbowRevisionSemantics.interpretation,iff_def] using hh

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

theorem positiveBooleanAxioms : Comparators.GorbowSortedBooleanTruth.PositiveBooleanAxioms :=
  fun initial k => closeBoolean _ (instances initial k)

theorem gorbowSortedBooleanTruth : Comparators.GorbowSortedBooleanTruth.Target :=
  ⟨guardCalibration,functionCalibration,positiveBooleanAxioms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanTruthProof
