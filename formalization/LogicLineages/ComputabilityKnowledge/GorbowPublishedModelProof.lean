module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! The published-D theorem-set model. Guard and implication-code semantics of
the real named overlay come from the actual named dispatchers and the
calibrated source programs. Pr_S semantics at arbitrary term values reduces
to the paid closed-numeral calibration, and Pr_D semantics to closed
deduction. Theorem codes are closed under modus ponens purely syntactically;
the finite S axioms are proved true first; S-soundness applied to the paid
published diagonal then gives the literal reflection sentence; only then is
D modelhood used to conclude consistency. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open List.Vector

/-! ### Named overlay guard and implication code -/

private theorem guardValue (pF pR : Program 1) (q : Program 5)
    (hR : ∀ x, evaluate pR (x ::ᵥ List.Vector.nil) =
      GorbowSourceRegistryPadding.sourceRelationValue x) (v : Nat) :
    GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR
        (GorbowRegistryTuple.header 1 0 [v]) = true ↔
      ∃ sigma : Sentence, GorbowSortedSyntaxCode.formulaCode sigma = v := by
  have h1 : GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR
        (GorbowRegistryTuple.header 1 0 [v]) = true ↔
      evaluate pR (GorbowRegistryTuple.header 1 0 [v] ::ᵥ List.Vector.nil) = 1 :=
    GorbowNamedRegistryInterpretation.Proof.namedRelation (augmented pF q) pR (1, 0)
      (by simp [GorbowSourceRegistryPadding.relationNames]) [v] rfl
  have h2 : evaluate pR (GorbowRegistryTuple.header 1 0 [v] ::ᵥ List.Vector.nil) = 1 ↔
      GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header 1 0 [v]) = true := by
    rw [hR]
    unfold GorbowSourceRegistryPadding.sourceRelationValue
    cases GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header 1 0 [v]) <;> simp
  have h3 : GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header 1 0 [v]) = true ↔
      ∃ sigma : Sentence, v = GorbowSortedSyntaxCode.formulaCode sigma := by
    rw [(GorbowSortedRegistryProof.relationDispatch v 0).1]
    exact GorbowSortedBooleanCodeProof.exactDomains.1 v
  exact h1.trans (h2.trans (h3.trans
    ⟨fun ⟨σ, h⟩ => ⟨σ, h.symm⟩, fun ⟨σ, h⟩ => ⟨σ, h.symm⟩⟩))

theorem guardCalibration : GorbowPublishedModel.Targets.GuardCalibration := by
  intro pF pR q c hA I n t env
  have hh : (GorbowRegistryTuple.headerTerm 1 0 [t]).realize (namedInterpretation pF pR q I) env =
      GorbowRegistryTuple.header 1 0 [t.realize (namedInterpretation pF pR q I) env] :=
    (GorbowRegistryTupleProof.termCalibration n (namedInterpretation pF pR q I) env).2.2 1 0 [t]
  show GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 1 0 [t]).realize (namedInterpretation pF pR q I) env) = true ↔ _
  rw [hh]
  exact guardValue pF pR q hA.1.2 _

private theorem implValue (pF pR : Program 1) (q : Program 5)
    (hF : ∀ x, evaluate (augmented pF q) (x ::ᵥ List.Vector.nil) =
      GorbowSourceRegistryPadding.sourceFunction x) (σ τ : Sentence) :
    GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
        (GorbowRegistryTuple.header 2 0
          [GorbowSortedSyntaxCode.formulaCode σ, GorbowSortedSyntaxCode.formulaCode τ]) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ) := by
  have hf : GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
        (GorbowRegistryTuple.header 2 0
          [GorbowSortedSyntaxCode.formulaCode σ, GorbowSortedSyntaxCode.formulaCode τ]) =
      evaluate (augmented pF q) (GorbowRegistryTuple.header 2 0
        [GorbowSortedSyntaxCode.formulaCode σ, GorbowSortedSyntaxCode.formulaCode τ] ::ᵥ
          List.Vector.nil) :=
    GorbowNamedRegistryInterpretation.Proof.namedFunction (augmented pF q) pR (2, 0)
      (by simp [GorbowSourceRegistryPadding.functionNames])
      [GorbowSortedSyntaxCode.formulaCode σ, GorbowSortedSyntaxCode.formulaCode τ] rfl
  rw [hf, hF]
  exact ((GorbowDiagonalRegistryProof.originalDispatch.2 (GorbowSortedSyntaxCode.formulaCode σ)
    (GorbowSortedSyntaxCode.formulaCode τ) 0).2.1).trans
    (GorbowSortedBooleanCodeProof.actualConstructors 0 σ τ).2.1

theorem implicationCalibration : GorbowPublishedModel.Targets.ImplicationCalibration := by
  intro pF pR q c hA I n s t env σ τ hs ht
  have hcal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  have hh : (GorbowRegistryTuple.headerTerm 2 0 [s, t]).realize (namedInterpretation pF pR q I) env =
      GorbowRegistryTuple.header 2 0 [s.realize (namedInterpretation pF pR q I) env,
        t.realize (namedInterpretation pF pR q I) env] :=
    (GorbowRegistryTupleProof.termCalibration n (namedInterpretation pF pR q I) env).2.2 2 0 [s, t]
  show GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
      ((GorbowRegistryTuple.headerTerm 2 0 [s, t]).realize (namedInterpretation pF pR q I) env) = _
  rw [hh, hs, ht]
  exact implValue pF pR q hcal.1 σ τ

/-! ### Pr_S and Pr_D semantics -/

theorem sProvabilityCalibration : GorbowPublishedModel.Targets.SProvabilityCalibration := by
  intro pF pR q c hA I n t env
  have e1 : (applyProv pF c t).realize (namedInterpretation pF pR q I) env ↔
      (provability pF c).realize (namedInterpretation pF pR q I)
        (fun _ => t.realize (namedInterpretation pF pR q I) env) := by
    unfold applyProv
    exact GorbowFormulaSubstitution.substituteFormula_realize _ _ _ _
  have e2 : (applyProv pF c (Term.numeral (t.realize (namedInterpretation pF pR q I) env))).realize
        (namedInterpretation pF pR q I) Fin.elim0 ↔
      (provability pF c).realize (namedInterpretation pF pR q I)
        (fun _ => t.realize (namedInterpretation pF pR q I) env) := by
    unfold applyProv
    rw [GorbowFormulaSubstitution.substituteFormula_realize]
    simp only [numeral_realize]
  have e3 := GorbowPublishedDCB.Proof.provabilityCalibration pF pR q c hA I
    (t.realize (namedInterpretation pF pR q I) env)
  exact e1.trans (e2.symm.trans (e3.trans
    ⟨fun ⟨σ, h, d⟩ => ⟨σ, h.symm, d⟩, fun ⟨σ, h, d⟩ => ⟨σ, h.symm, d⟩⟩))

theorem dProvabilityCalibration : GorbowPublishedModel.Targets.DProvabilityCalibration := by
  intro pF pR q c hA I σ
  have hb : (GorbowBooleanTruth.binaryCodeTerm 0
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode σ)) : Term 0).realize
        (namedInterpretation pF pR q I) Fin.elim0 =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) σ) :=
    implicationCalibration pF pR q c hA I 0 _ _ Fin.elim0 (rho pF c) σ
      (numeral_realize _ _ _) (numeral_realize _ _ _)
  have hs := sProvabilityCalibration pF pR q c hA I 0
    (GorbowBooleanTruth.binaryCodeTerm 0
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode σ))) Fin.elim0
  rw [hb] at hs
  have hc := GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) σ
  constructor
  · intro hp
    obtain ⟨τ, hτ, hd⟩ := hs.mp hp
    have hτ' : τ = Formula.imp (rho pF c) σ :=
      GorbowSortedSyntaxCodeProof.actualInjection.1 0 hτ
    subst hτ'
    exact hc.mpr hd
  · intro hd
    exact hs.mpr ⟨_, rfl, hc.mp hd⟩

/-! ### Syntactic modus-ponens closure of the theorem codes -/

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

/-! ### The finite S axioms hold in the theorem-set model -/

private theorem bridgeTrue (pF pR : Program 1) (q : Program 5) (c : Code) :
    GorbowSortedKnowledgeAxioms.bridge.realize (theoremModel pF pR q c) Fin.elim0 := by
  intro x _
  exact ⟨fun hP a ha => ⟨ha, hP⟩, fun h => (h 0 rfl).2⟩

private theorem distTrue (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    GorbowSortedKnowledgeAxioms.distribution.realize (theoremModel pF pR q c) Fin.elim0 := by
  intro a ha φ hφ ψ hψ hk
  obtain ⟨σ, hσ⟩ := (guardCalibration pF pR q c hA (theoremModel pF pR q c) _ _ _).mp hφ
  obtain ⟨τ, hτ⟩ := (guardCalibration pF pR q c hA (theoremModel pF pR q c) _ _ _).mp hψ
  have hσ' : GorbowSortedSyntaxCode.formulaCode σ = φ := hσ
  have hτ' : GorbowSortedSyntaxCode.formulaCode τ = ψ := hτ
  have hb : (GorbowBooleanTruth.binaryCodeTerm 0 (Term.var 1) (Term.var 0) : Term 3).realize
      (namedInterpretation pF pR q (theoremModel pF pR q c))
      (Fin.cases ψ (Fin.cases φ (Fin.cases a Fin.elim0))) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ) :=
    implicationCalibration pF pR q c hA _ 3 _ _ _ σ τ hσ'.symm hτ'.symm
  obtain ⟨⟨_, hPσ⟩, ⟨_, hPb⟩⟩ := hk
  have hPb' : theoremCodes pF pR q c (GorbowSortedSyntaxCode.formulaCode (Formula.imp σ τ)) := by
    rw [← hb]
    exact hPb
  have hPσ' : theoremCodes pF pR q c (GorbowSortedSyntaxCode.formulaCode σ) := by
    rw [hσ']
    exact hPσ
  refine ⟨ha, ?_⟩
  show theoremCodes pF pR q c ψ
  rw [← hτ']
  exact codesMP hPb' hPσ'

private theorem sAxiomsTrue (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    ∀ σ, S pF pR q σ → σ.realize (theoremModel pF pR q c) Fin.elim0 := by
  intro σ hσ
  rcases List.mem_append.mp hσ with h | h
  · rcases List.mem_append.mp h with h1 | h2
    · exact GorbowNamedDefiningTheory.Proof.internalEquationsSound (augmented pF q) pR
        (theoremModel pF pR q c) σ h1
    · exact GorbowNamedDefiningTheory.Proof.aliasesSound (augmented pF q) pR
        (theoremModel pF pR q c) σ h2
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, rfl⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact bridgeTrue pF pR q c
    rcases List.mem_cons.mp h with rfl | h
    · exact distTrue pF pR q c hA
    · cases h

/-! ### The literal reflection sentence -/

private theorem reflectionTrue (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) (v : Fin 1 → Nat)
    (hv : v 0 = GorbowSortedSyntaxCode.formulaCode (rho pF c)) :
    (reflectionTemplate pF c).realize (theoremModel pF pR q c) v := by
  intro a ha x hx hp
  obtain ⟨σ, hσ⟩ := (guardCalibration pF pR q c hA (theoremModel pF pR q c) _ _ _).mp hx
  have hσ' : GorbowSortedSyntaxCode.formulaCode σ = x := hσ
  have hb : (GorbowBooleanTruth.binaryCodeTerm 0 (Term.var 2) (Term.var 0) : Term 3).realize
      (namedInterpretation pF pR q (theoremModel pF pR q c)) (Fin.cases x (Fin.cases a v)) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) σ) :=
    implicationCalibration pF pR q c hA _ 3 _ _ _ (rho pF c) σ hv hσ'.symm
  obtain ⟨τ, hτ, hd⟩ :=
    (sProvabilityCalibration pF pR q c hA (theoremModel pF pR q c) _ _ _).mp hp
  have hτ' : GorbowSortedSyntaxCode.formulaCode τ =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp (rho pF c) σ) := hτ.trans hb
  have hτe : τ = Formula.imp (rho pF c) σ := GorbowSortedSyntaxCodeProof.actualInjection.1 0 hτ'
  subst hτe
  have hD : Nonempty (Derivation (D pF pR q c) σ) :=
    (GorbowClosedDeductionProof.closedExtension (S pF pR q) (rho pF c) σ).mpr hd
  refine ⟨ha, ?_⟩
  show theoremCodes pF pR q c x
  exact ⟨σ, hσ', hD⟩

/-- Staged at an abstract formula/value, so the actual diagonal code is never
expanded while matching the valuation dictionary. -/
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

/-- Reduce the semantic biconditional at abstract sentences before supplying
its actual self-referential arguments. -/
private theorem provedBiconditionalTrue (T : Sentence → Prop) (a b : Sentence)
    (d : Derivation T (GorbowBooleanTruth.biconditional a b)) (I : Interpretation)
    (hT : ∀ sigma, T sigma → sigma.realize I Fin.elim0) :
    a.realize I Fin.elim0 ↔ b.realize I Fin.elim0 := by
  have h := GorbowTheoryProofProof.theorySoundness T 0 _ d I hT Fin.elim0
  exact ⟨h.1, h.2⟩

private theorem rhoTrue (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) :
    (rho pF c).realize (theoremModel pF pR q c) Fin.elim0 := by
  have hr : (reflectionTemplate pF c).realize (theoremModel pF pR q c)
      (fun _ : Fin 1 => GorbowSortedSyntaxCode.formulaCode (rho pF c)) :=
    reflectionTrue pF pR q c hA _ rfl
  have hR := closedInstanceTrue (reflectionTemplate pF c) (theoremModel pF pR q c)
    (GorbowSortedSyntaxCode.formulaCode (rho pF c)) hr
  obtain ⟨hdiag⟩ := GorbowPublishedDCB.Proof.publishedDiagonal pF pR q c hA.1
  have hb := provedBiconditionalTrue (S pF pR q) (rho pF c)
    (GorbowStandardInstances.instantiate (reflectionTemplate pF c)
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))))
    hdiag (theoremModel pF pR q c) (sAxiomsTrue pF pR q c hA)
  exact hb.mpr hR

/-! ### D modelhood and consistency -/

theorem theoremSetModel : GorbowPublishedModel.Targets.TheoremSetModel := by
  intro pF pR q c hA σ hσ
  rcases hσ with h | rfl
  · exact sAxiomsTrue pF pR q c hA σ h
  · exact rhoTrue pF pR q c hA

theorem consistency : GorbowPublishedModel.Targets.Consistency := by
  intro pF pR q c hA hd
  obtain ⟨d⟩ := hd
  exact falseEquality_not_realized _
    (GorbowTheoryProofProof.theorySoundness (D pF pR q c) 0 _ d (theoremModel pF pR q c)
      (theoremSetModel pF pR q c hA) Fin.elim0)

theorem fullTarget : GorbowPublishedModel.Targets.Target :=
  ⟨guardCalibration, implicationCalibration, sProvabilityCalibration, dProvabilityCalibration,
    theoremSetModel, consistency⟩

end LogicLineages.ComputabilityKnowledge.GorbowPublishedModel.Proof
