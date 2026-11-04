module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruthTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof

@[expose] public section
/-! Coded Boolean truth composition on the real published-D ground. The guard
is R013's named-overlay guard calibration, applied to an interpretation whose
overlay reinstalls its own fields. All four code constructors are calibrated
through the actual named function dispatcher, the augmented source
calibration and the source constructor numbers. The paid ground-generic
positive-revision Boolean composition then gives the four literal coded
axioms at every actual positive stage. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB GorbowPublishedModel
open GorbowBooleanTruth GorbowSortedRevision GorbowSortedSyntaxCode

/-! ### Guard on the actual ground -/

theorem groundGuard : GorbowPublishedBooleanTruth.Targets.GroundGuard := by
  intro pF pR q c hA P n t env
  exact GorbowPublishedModel.Proof.guardCalibration pF pR q c hA
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) n t env

/-! ### The four code constructors on the actual ground -/

private theorem namedValue (pF pR : Program 1) (q : Program 5)
    (hF : ∀ x, evaluate (augmented pF q) (x ::ᵥ List.Vector.nil) =
      GorbowSourceRegistryPadding.sourceFunction x)
    (name : Nat × Nat) (hn : name ∈ GorbowSourceRegistryPadding.functionNames)
    (args : List Nat) (hlen : args.length = name.1) :
    GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
        (GorbowRegistryTuple.header name.1 name.2 args) =
      GorbowDiagonalRegistry.functionProgram (GorbowRegistryTuple.header name.1 name.2 args) :=
  (GorbowNamedRegistryInterpretation.Proof.namedFunction (augmented pF q) pR name hn args hlen).trans
    (hF _)

attribute [local irreducible] GorbowRegistryTuple.headerTerm GorbowRegistryTuple.pairTerm
  GorbowRegistryTuple.tupleTerm

private theorem negFunction (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (n : Nat) (s t : Term n)
    (env : Fin n → Nat) (σ τ : Sentence)
    (hs : s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode σ)
    (ht : t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode τ) :
    (negCodeTerm s).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.neg σ) := by
  have hF := (GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1).1
  have hdisp := GorbowDiagonalRegistryProof.originalDispatch.2 (formulaCode σ) (formulaCode τ) 0
  have hcons := GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ
  have h1 : (GorbowRegistryTuple.headerTerm 1 0 [s]).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      GorbowRegistryTuple.header 1 0
        [s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env] :=
    (GorbowRegistryTupleProof.termCalibration n
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env).2.2 1 0 [s]
  show GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 1 0 [s]).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env) = _
  rw [h1, hs]
  exact (namedValue pF pR q hF (1, 0) (by simp [GorbowSourceRegistryPadding.functionNames])
    [formulaCode σ] rfl).trans (hdisp.1.trans hcons.1)

private theorem impFunction (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (n : Nat) (s t : Term n)
    (env : Fin n → Nat) (σ τ : Sentence)
    (hs : s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode σ)
    (ht : t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode τ) :
    (binaryCodeTerm 0 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.imp σ τ) := by
  have hF := (GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1).1
  have hdisp := GorbowDiagonalRegistryProof.originalDispatch.2 (formulaCode σ) (formulaCode τ) 0
  have hcons := GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ
  have h2 : ∀ tag : Nat, (GorbowRegistryTuple.headerTerm 2 tag [s, t]).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      GorbowRegistryTuple.header 2 tag
        [s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env,
          t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env] :=
    fun tag => (GorbowRegistryTupleProof.termCalibration n
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env).2.2 2 tag [s, t]
  show GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 2 0 [s, t]).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env) = _
  rw [h2, hs, ht]
  exact (namedValue pF pR q hF (2, 0) (by simp [GorbowSourceRegistryPadding.functionNames])
    [formulaCode σ, formulaCode τ] rfl).trans (hdisp.2.1.trans hcons.2.1)

private theorem conjFunction (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (n : Nat) (s t : Term n)
    (env : Fin n → Nat) (σ τ : Sentence)
    (hs : s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode σ)
    (ht : t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode τ) :
    (binaryCodeTerm 1 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.conj σ τ) := by
  have hF := (GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1).1
  have hdisp := GorbowDiagonalRegistryProof.originalDispatch.2 (formulaCode σ) (formulaCode τ) 0
  have hcons := GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ
  have h2 : ∀ tag : Nat, (GorbowRegistryTuple.headerTerm 2 tag [s, t]).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      GorbowRegistryTuple.header 2 tag
        [s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env,
          t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env] :=
    fun tag => (GorbowRegistryTupleProof.termCalibration n
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env).2.2 2 tag [s, t]
  show GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 2 1 [s, t]).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env) = _
  rw [h2, hs, ht]
  exact (namedValue pF pR q hF (2, 1) (by simp [GorbowSourceRegistryPadding.functionNames])
    [formulaCode σ, formulaCode τ] rfl).trans (hdisp.2.2.1.trans hcons.2.2.1)

private theorem disjFunction (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (n : Nat) (s t : Term n)
    (env : Fin n → Nat) (σ τ : Sentence)
    (hs : s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode σ)
    (ht : t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode τ) :
    (binaryCodeTerm 2 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.disj σ τ) := by
  have hF := (GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1).1
  have hdisp := GorbowDiagonalRegistryProof.originalDispatch.2 (formulaCode σ) (formulaCode τ) 0
  have hcons := GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ
  have h2 : ∀ tag : Nat, (GorbowRegistryTuple.headerTerm 2 tag [s, t]).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      GorbowRegistryTuple.header 2 tag
        [s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env,
          t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env] :=
    fun tag => (GorbowRegistryTupleProof.termCalibration n
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env).2.2 2 tag [s, t]
  show GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 2 2 [s, t]).realize
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env) = _
  rw [h2, hs, ht]
  exact (namedValue pF pR q hF (2, 2) (by simp [GorbowSourceRegistryPadding.functionNames])
    [formulaCode σ, formulaCode τ] rfl).trans (hdisp.2.2.2.1.trans hcons.2.2.2)

theorem booleanFunctions : GorbowPublishedBooleanTruth.Targets.BooleanFunctions := by
  intro pF pR q c hA P n s t env σ τ hs ht
  exact ⟨negFunction pF pR q c hA P n s t env σ τ hs ht,
    impFunction pF pR q c hA P n s t env σ τ hs ht,
    conjFunction pF pR q c hA P n s t env σ τ hs ht,
    disjFunction pF pR q c hA P n s t env σ τ hs ht⟩

/-! ### Positive-stage truth composition on the actual ground -/

private theorem truthCodes (g : Ground) (initial : Extension) (k : Nat) (σ τ : Sentence) :
    (extensions g initial (k+1) (formulaCode (.neg σ)) ↔
      ¬ extensions g initial (k+1) (formulaCode σ)) ∧
    (extensions g initial (k+1) (formulaCode (.imp σ τ)) ↔
      (extensions g initial (k+1) (formulaCode σ) → extensions g initial (k+1) (formulaCode τ))) ∧
    (extensions g initial (k+1) (formulaCode (.conj σ τ)) ↔
      (extensions g initial (k+1) (formulaCode σ) ∧ extensions g initial (k+1) (formulaCode τ))) ∧
    (extensions g initial (k+1) (formulaCode (.disj σ τ)) ↔
      (extensions g initial (k+1) (formulaCode σ) ∨ extensions g initial (k+1) (formulaCode τ))) := by
  simpa [truthSentence, formulaQuote, Formula.realize, numeral_realize, stage, interpretation,
    GorbowRevisionSemantics.interpretation] using
    GorbowSortedRevisionCompositionProof.booleanTruth g initial k σ τ

private theorem instances (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (k n : Nat) (s t : Term n) (ρ : Fin n → Nat)
    (hs : (sentenceGuard s).realize (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ)
    (ht : (sentenceGuard t).realize (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ) :
    (biconditional (.truth (negCodeTerm s)) (.neg (.truth s))).realize
      (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 0 s t)) (.imp (.truth s) (.truth t))).realize
      (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 1 s t)) (.conj (.truth s) (.truth t))).realize
      (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ ∧
    (biconditional (.truth (binaryCodeTerm 2 s t)) (.disj (.truth s) (.truth t))).realize
      (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1)) ρ := by
  obtain ⟨σ, hσ0⟩ := (groundGuard pF pR q c hA
    (extensions (ground pF pR q) (theoremCodes pF pR q c) (k+1)) n s ρ).mp hs
  obtain ⟨τ, hτ0⟩ := (groundGuard pF pR q c hA
    (extensions (ground pF pR q) (theoremCodes pF pR q c) (k+1)) n t ρ).mp ht
  have hσ := hσ0.symm
  have hτ := hτ0.symm
  obtain ⟨hn, hi, hc, hd⟩ := booleanFunctions pF pR q c hA
    (extensions (ground pF pR q) (theoremCodes pF pR q c) (k+1)) n s t ρ σ τ hσ hτ
  have hh := truthCodes (ground pF pR q) (theoremCodes pF pR q c) k σ τ
  simp only [stage, interpretation, GorbowRevisionSemantics.interpretation] at hn hi hc hd hσ hτ
  simpa only [biconditional, Formula.realize, hn, hi, hc, hd, hσ, hτ, stage, interpretation,
    GorbowRevisionSemantics.interpretation, iff_def] using hh

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

theorem positiveBooleanAxioms : GorbowPublishedBooleanTruth.Targets.PositiveBooleanAxioms := by
  intro pF pR q c hA k
  exact closeBoolean (stage (ground pF pR q) (theoremCodes pF pR q c) (k+1))
    (instances pF pR q c hA k)

theorem fullTarget : GorbowPublishedBooleanTruth.Targets.Target :=
  ⟨groundGuard, booleanFunctions, positiveBooleanAxioms⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.Proof
