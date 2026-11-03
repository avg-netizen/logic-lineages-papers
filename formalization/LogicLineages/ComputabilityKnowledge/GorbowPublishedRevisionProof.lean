module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedRevisionTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! Sorted revision on the real published-D ground. R013's actual D-model
argument is generalized to any extension that contains the actual D theorem
codes and is closed under literal-sentence modus ponens. A joint induction
then proves both properties for every actual stage: the successor inclusion
uses prior-stage D soundness and the exact revision image; successor modus
ponens closure is the paid positive-revision distribution; only then is the
successor D model built. No monotonicity of the revision sequence is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB GorbowPublishedModel

/-! ### Syntactic modus ponens for the initial theorem codes -/

private theorem codesMP {pF pR : Program 1} {q : Program 5} {c : Code} {σ τ : Sentence}
    (h1 : theoremCodes pF pR q c (GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ)))
    (h2 : theoremCodes pF pR q c (GorbowSortedSyntaxCode.formulaCode σ)) :
    theoremCodes pF pR q c (GorbowSortedSyntaxCode.formulaCode τ) := by
  obtain ⟨a, ha, ⟨da⟩⟩ := h1
  obtain ⟨b, hb, ⟨db⟩⟩ := h2
  have ha' : a = Formula.imp σ τ := GorbowSortedSyntaxCodeProof.actualInjection.1 0 ha
  have hb' : b = σ := GorbowSortedSyntaxCodeProof.actualInjection.1 0 hb
  subst ha'
  subst hb'
  exact ⟨τ, rfl, ⟨.mp da db⟩⟩

/-! ### The S axioms at an arbitrary admissible extension -/

private theorem bridgeTrueP (pF pR : Program 1) (q : Program 5) (P : Nat → Prop) :
    GorbowSortedKnowledgeAxioms.bridge.realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  intro x _
  exact ⟨fun hP a ha => ⟨ha, hP⟩, fun h => (h 0 rfl).2⟩

private theorem distTrueP (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (hMP : ModusPonensClosed P) :
    GorbowSortedKnowledgeAxioms.distribution.realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  intro a ha φ hφ ψ hψ hk
  obtain ⟨σ, hσ⟩ := (GorbowPublishedModel.Proof.guardCalibration pF pR q c hA
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) _ _ _).mp hφ
  obtain ⟨τ, hτ⟩ := (GorbowPublishedModel.Proof.guardCalibration pF pR q c hA
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) _ _ _).mp hψ
  have hσ' : GorbowSortedSyntaxCode.formulaCode σ = φ := hσ
  have hτ' : GorbowSortedSyntaxCode.formulaCode τ = ψ := hτ
  have hb : (GorbowBooleanTruth.binaryCodeTerm 0 (Term.var 1) (Term.var 0) : Term 3).realize
      (namedInterpretation pF pR q (GorbowRevisionSemantics.interpretation (ground pF pR q) P))
      (Fin.cases ψ (Fin.cases φ (Fin.cases a Fin.elim0))) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ) :=
    GorbowPublishedModel.Proof.implicationCalibration pF pR q c hA _ 3 _ _ _ σ τ
      hσ'.symm hτ'.symm
  obtain ⟨⟨_, hPσ⟩, ⟨_, hPb⟩⟩ := hk
  have hPb' : P (GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ)) := by
    rw [← hb]
    exact hPb
  have hPσ' : P (GorbowSortedSyntaxCode.formulaCode σ) := by
    rw [hσ']
    exact hPσ
  refine ⟨ha, ?_⟩
  show P ψ
  rw [← hτ']
  exact hMP σ τ hPσ' hPb'

private theorem sAxiomsTrueP (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (hMP : ModusPonensClosed P) :
    ∀ σ, S pF pR q σ →
      σ.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  intro σ hσ
  rcases List.mem_append.mp hσ with h | h
  · rcases List.mem_append.mp h with h1 | h2
    · exact GorbowNamedDefiningTheory.Proof.internalEquationsSound (augmented pF q) pR
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) σ h1
    · exact GorbowNamedDefiningTheory.Proof.aliasesSound (augmented pF q) pR
        (GorbowRevisionSemantics.interpretation (ground pF pR q) P) σ h2
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, rfl⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact bridgeTrueP pF pR q P
    rcases List.mem_cons.mp h with rfl | h
    · exact distTrueP pF pR q c hA P hMP
    · cases h

/-! ### The literal reflection sentence at an admissible extension -/

private theorem reflectionTrueP (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (hInc : IncludesTheorems pF pR q c P)
    (v : Fin 1 → Nat) (hv : v 0 = GorbowSortedSyntaxCode.formulaCode (rho pF c)) :
    (reflectionTemplate pF c).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P) v := by
  intro a ha x hx hp
  obtain ⟨σ, hσ⟩ := (GorbowPublishedModel.Proof.guardCalibration pF pR q c hA
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) _ _ _).mp hx
  have hσ' : GorbowSortedSyntaxCode.formulaCode σ = x := hσ
  have hb : (GorbowBooleanTruth.binaryCodeTerm 0 (Term.var 2) (Term.var 0) : Term 3).realize
      (namedInterpretation pF pR q (GorbowRevisionSemantics.interpretation (ground pF pR q) P))
      (Fin.cases x (Fin.cases a v)) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) σ) :=
    GorbowPublishedModel.Proof.implicationCalibration pF pR q c hA _ 3 _ _ _ (rho pF c) σ
      hv hσ'.symm
  obtain ⟨τ, hτ, hd⟩ := (GorbowPublishedModel.Proof.sProvabilityCalibration pF pR q c hA
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P) _ _ _).mp hp
  have hτ' : GorbowSortedSyntaxCode.formulaCode τ =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) σ) := hτ.trans hb
  have hτe : τ = Formula.imp (rho pF c) σ := GorbowSortedSyntaxCodeProof.actualInjection.1 0 hτ'
  subst hτe
  have hD : Nonempty (Derivation (D pF pR q c) σ) :=
    (GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) σ).mpr hd
  refine ⟨ha, ?_⟩
  show P x
  exact hInc x ⟨σ, hσ', hD⟩

/-- Staged at an abstract formula/value, so the diagonal code is never expanded. -/
private theorem closedInstanceTrue (phi : Formula 1) (I : Interpretation) (value : Nat)
    (h : phi.realize I (fun _ : Fin 1 => value)) :
    (GorbowStandardInstances.instantiate phi (Term.numeral value)).realize I Fin.elim0 := by
  unfold GorbowStandardInstances.instantiate
  apply (GorbowFormulaSubstitution.substituteFormula_realize phi I Fin.elim0
    (Fin.cases (Term.numeral value) Term.var : Fin 1 → Term 0)).mpr
  have hd : (fun i : Fin 1 =>
      ((Fin.cases (Term.numeral value) Term.var : Fin 1 → Term 0) i).realize I Fin.elim0) =
      (fun _ : Fin 1 => value) := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact numeral_realize I Fin.elim0 value
  rw [hd]
  exact h

/-- The semantic biconditional at abstract sentences, by actual soundness. -/
private theorem provedBiconditionalTrue (T : Sentence → Prop) (a b : Sentence)
    (d : Derivation T (GorbowBooleanTruth.biconditional a b)) (I : Interpretation)
    (hT : ∀ sigma, T sigma → sigma.realize I Fin.elim0) :
    a.realize I Fin.elim0 ↔ b.realize I Fin.elim0 := by
  have h := GorbowTheoryProofProof.theorySoundness T 0 _ d I hT Fin.elim0
  exact ⟨h.1, h.2⟩

private theorem rhoTrueP (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (P : Nat → Prop) (hInc : IncludesTheorems pF pR q c P)
    (hMP : ModusPonensClosed P) :
    (rho pF c).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0 := by
  have hr : (reflectionTemplate pF c).realize
      (GorbowRevisionSemantics.interpretation (ground pF pR q) P)
      (fun _ : Fin 1 => GorbowSortedSyntaxCode.formulaCode (rho pF c)) :=
    reflectionTrueP pF pR q c hA P hInc _ rfl
  have hR := closedInstanceTrue (reflectionTemplate pF c)
    (GorbowRevisionSemantics.interpretation (ground pF pR q) P)
    (GorbowSortedSyntaxCode.formulaCode (rho pF c)) hr
  obtain ⟨hdiag⟩ := GorbowPublishedDCB.Proof.publishedDiagonal pF pR q c hA.1
  have hb := provedBiconditionalTrue (S pF pR q) (rho pF c)
    (GorbowStandardInstances.instantiate (reflectionTemplate pF c)
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))))
    hdiag (GorbowRevisionSemantics.interpretation (ground pF pR q) P)
    (sAxiomsTrueP pF pR q c hA P hMP)
  exact hb.mpr hR

theorem extensionModel : GorbowPublishedRevision.Targets.ExtensionModel := by
  intro pF pR q c hA P hInc hMP σ hσ
  rcases hσ with h | rfl
  · exact sAxiomsTrueP pF pR q c hA P hMP σ h
  · exact rhoTrueP pF pR q c hA P hInc hMP

/-! ### Joint induction over the actual sorted revision stages -/

private theorem joint (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : ∀ n,
    IncludesTheorems pF pR q c (extension pF pR q c n) ∧
      ModusPonensClosed (extension pF pR q c n) := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun code h => h, fun σ τ h1 h2 => codesMP h2 h1⟩
  | succ n ih =>
    have hAx : ∀ σ, D pF pR q c σ → σ.realize (stage pF pR q c n) Fin.elim0 :=
      fun σ h => extensionModel pF pR q c hA _ ih.1 ih.2 σ h
    refine ⟨?_, ?_⟩
    · intro code hcode
      obtain ⟨σ, hσ, ⟨d⟩⟩ := hcode
      have ht : σ.realize (stage pF pR q c n) Fin.elim0 :=
        GorbowTheoryProofProof.theorySoundness (D pF pR q c) 0 σ d (stage pF pR q c n) hAx
          Fin.elim0
      rw [← hσ]
      show GorbowSortedRevision.revise (ground pF pR q) (extension pF pR q c n)
        (GorbowSortedSyntaxCode.formulaCode σ)
      exact ((GorbowSortedRevisionProof.exactImage (ground pF pR q)
        (extension pF pR q c n)).1 σ).mpr ht
    · intro σ τ hσ hi
      exact GorbowSortedRevisionProof.positiveDistribution (ground pF pR q)
        (theoremCodes pF pR q c) n σ τ hi hσ

theorem stageAxioms : GorbowPublishedRevision.Targets.StageAxioms := by
  intro pF pR q c hA n σ hσ
  obtain ⟨hi, hm⟩ := joint pF pR q c hA n
  exact extensionModel pF pR q c hA _ hi hm σ hσ

theorem stageTheorems : GorbowPublishedRevision.Targets.StageTheorems := by
  intro pF pR q c hA n σ hd
  obtain ⟨d⟩ := hd
  exact GorbowTheoryProofProof.theorySoundness (D pF pR q c) 0 σ d (stage pF pR q c n)
    (stageAxioms pF pR q c hA n) Fin.elim0

theorem theoremCodePersistence : GorbowPublishedRevision.Targets.TheoremCodePersistence := by
  intro pF pR q c hA n
  exact (joint pF pR q c hA n).1

theorem fullTarget : GorbowPublishedRevision.Targets.Target :=
  ⟨extensionModel, stageAxioms, stageTheorems, theoremCodePersistence⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.Proof
