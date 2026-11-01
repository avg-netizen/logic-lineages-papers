module

public import LogicLineages.ComputabilityKnowledge.GorbowSelectedDistributionTargets
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowDiagonalRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedBooleanCodeProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
/-! Proofs for selected-agent distribution. Sentence guards and the
implication-code equation are derived from the named numeral certificates of
the calibrated source dispatchers. The selected-agent closure is an ordinary
Hilbert derivation: the closed premises are discharged by the closed deduction
theorem, the agent stays a free variable of context one, the single universal
K2 axiom is instantiated by `allInstantiate`, equality replacement moves the
implication code, and `generalize` closes the agent. No omega-rule, semantic
validity or extra proof constructor is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.Proof
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution List.Vector

/-! ### Actual programs and the axiom checker -/

theorem actualPrograms : GorbowSelectedDistribution.Targets.ActualPrograms := by
  obtain ⟨_, _, pF, pR, hF, hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  exact ⟨pF, pR, hF, hR⟩

theorem numericAxiomChecker : GorbowSelectedDistribution.Targets.NumericAxiomChecker := by
  intro pF pR
  refine ⟨?_, ?_⟩
  · have hN := GorbowNamedDefiningTheory.Proof.fixedCheckerPrimitive pF pR
    have hE : Primrec (fun raw : List Nat =>
        decide (raw = GorbowFormulaPrefixCode.encode GorbowSortedKnowledgeAxioms.distribution)) :=
      (Primrec.eq.comp (Primrec.id : Primrec (fun x : List Nat => x))
        (Primrec.const (GorbowFormulaPrefixCode.encode
          GorbowSortedKnowledgeAxioms.distribution))).decide
    exact (Primrec.or.comp hN hE).of_eq (fun raw => rfl)
  · funext sigma
    apply propext
    show (GorbowNamedDefiningTheory.check pF pR (GorbowFormulaPrefixCode.encode sigma) ||
        decide (GorbowFormulaPrefixCode.encode sigma =
          GorbowFormulaPrefixCode.encode GorbowSortedKnowledgeAxioms.distribution)) = true ↔
      (GorbowNamedDefiningTheory.Theory pF pR sigma ∨
        sigma = GorbowSortedKnowledgeAxioms.distribution)
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rw [GorbowNamedDefiningTheory.Proof.checkExact pF pR (GorbowFormulaPrefixCode.encode sigma)]
    have hinj := GorbowFormulaPrefixCodeProof.encodingInjective 0
    constructor
    · rintro (⟨s, hs, he⟩ | he)
      · have hsig := hinj he
        subst hsig
        exact Or.inl hs
      · exact Or.inr (hinj he)
    · rintro (hs | hs)
      · exact Or.inl ⟨sigma, hs, rfl⟩
      · exact Or.inr (congrArg GorbowFormulaPrefixCode.encode hs)

/-! ### Literal coding certificates -/

private theorem guardCertificate (pF pR : GorbowPRProgram.Program 1) (hcal : Calibrated pF pR)
    (sigma : Sentence) : Nonempty (Derivation (Theory pF pR) (sentenceGuard sigma)) := by
  have hmem : ((1, 0) : Nat × Nat) ∈ GorbowSourceRegistryPadding.relationNames := by
    simp [GorbowSourceRegistryPadding.relationNames]
  have hs : GorbowSortedRegistry.relationProgram
      (GorbowRegistryTuple.header 1 0 [GorbowSortedSyntaxCode.formulaCode sigma]) = true :=
    (GorbowSortedRegistryProof.relationDispatch (GorbowSortedSyntaxCode.formulaCode sigma) 0).1.trans
      ((GorbowSortedBooleanCodeProof.exactDomains.1 _).mpr ⟨sigma, rfl⟩)
  have hv : GorbowPRProgram.evaluate pR (GorbowNamedNumeralCertificates.inputCode (1, 0)
      (GorbowSortedSyntaxCode.formulaCode sigma ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = 1 := by
    rw [hcal.2]
    show (if GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header 1 0
      [GorbowSortedSyntaxCode.formulaCode sigma]) then 1 else 0) = 1
    simp [hs]
  obtain ⟨h⟩ := (GorbowNamedNumeralCertificates.Proof.namedRelationCalculation pF pR (1, 0) hmem
    (GorbowSortedSyntaxCode.formulaCode sigma ::ᵥ List.Vector.nil)).1 hv
  exact GorbowTheoryProofProof.monotonicity (GorbowNamedDefiningTheory.Theory pF pR)
    (Theory pF pR) (fun _ hs => Or.inl hs) 0 _ ⟨h⟩

private theorem implicationCertificate (pF pR : GorbowPRProgram.Program 1)
    (hcal : Calibrated pF pR) (sigma tau : Sentence) :
    Nonempty (Derivation (Theory pF pR) (implicationCode sigma tau)) := by
  have hmem : ((2, 0) : Nat × Nat) ∈ GorbowSourceRegistryPadding.functionNames := by
    simp [GorbowSourceRegistryPadding.functionNames]
  obtain ⟨h⟩ := GorbowNamedNumeralCertificates.Proof.namedFunctionCalculation pF pR (2, 0) hmem
    (GorbowSortedSyntaxCode.formulaCode sigma ::ᵥ GorbowSortedSyntaxCode.formulaCode tau ::ᵥ
      List.Vector.nil)
  have hval : GorbowPRProgram.evaluate pF (GorbowNamedNumeralCertificates.inputCode (2, 0)
      (GorbowSortedSyntaxCode.formulaCode sigma ::ᵥ GorbowSortedSyntaxCode.formulaCode tau ::ᵥ
        List.Vector.nil) ::ᵥ List.Vector.nil) =
      GorbowSortedSyntaxCode.formulaCode (Formula.imp sigma tau) := by
    rw [hcal.1]
    exact ((GorbowDiagonalRegistryProof.originalDispatch.2 (GorbowSortedSyntaxCode.formulaCode sigma)
      (GorbowSortedSyntaxCode.formulaCode tau) 0).2.1).trans
      (GorbowSortedBooleanCodeProof.actualConstructors 0 sigma tau).2.1
  rw [hval] at h
  exact GorbowTheoryProofProof.monotonicity (GorbowNamedDefiningTheory.Theory pF pR)
    (Theory pF pR) (fun _ hs => Or.inl hs) 0 _ ⟨h⟩

theorem literalCodingCertificates :
    GorbowSelectedDistribution.Targets.LiteralCodingCertificates :=
  fun pF pR hcal => ⟨guardCertificate pF pR hcal, implicationCertificate pF pR hcal⟩

/-! ### Hilbert combinators in an arbitrary context -/

private def liftK {A : Sentence → Prop} {n : Nat} {a : Formula n} (r : Formula n)
    (p : Derivation A a) : Derivation A (.imp r a) :=
  .mp (.logical (.k a r)) p

private def compose {A : Sentence → Prop} {n : Nat} {a b c : Formula n}
    (p : Derivation A (.imp b c)) (q : Derivation A (.imp a b)) : Derivation A (.imp a c) :=
  .mp (.mp (.logical (.s a b c)) (liftK a p)) q

private def mpUnder {A : Sentence → Prop} {n : Nat} {a x y : Formula n}
    (p : Derivation A (.imp a (.imp x y))) (q : Derivation A (.imp a x)) :
    Derivation A (.imp a y) :=
  .mp (.mp (.logical (.s a x y)) p) q

private def mpUnder2 {A : Sentence → Prop} {n : Nat} {a b x y : Formula n}
    (p : Derivation A (.imp a (.imp b (.imp x y)))) (q : Derivation A (.imp a (.imp b x))) :
    Derivation A (.imp a (.imp b y)) :=
  have hs : Derivation A (.imp (.imp b (.imp x y)) (.imp (.imp b x) (.imp b y))) :=
    .logical (.s b x y)
  mpUnder (mpUnder (liftK a hs) p) q

private def const2 {A : Sentence → Prop} {n : Nat} {x : Formula n} (a b : Formula n)
    (p : Derivation A x) : Derivation A (.imp a (.imp b x)) :=
  liftK a (liftK b p)

private def weakenUnder {A : Sentence → Prop} {n : Nat} {a x : Formula n} (b : Formula n)
    (p : Derivation A (.imp a x)) : Derivation A (.imp a (.imp b x)) :=
  have hk : Derivation A (.imp x (.imp b x)) := .logical (.k x b)
  compose hk p

/-! ### Syntactic transport into the one-agent context -/

private theorem substNum {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute σ (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n σ k

private theorem substHeader {m n : Nat} (σ : Fin m → Term n) (arity tag : Nat)
    (as : List (Term m)) :
    GorbowSubstitution.substitute σ (GorbowRegistryTuple.headerTerm arity tag as) =
      GorbowRegistryTuple.headerTerm arity tag (as.map (GorbowSubstitution.substitute σ)) :=
  GorbowHeaderSubstitutionProof.headers m n σ arity tag as

private theorem liftVariables (n : Nat) :
    liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (φ : Formula n) : substituteFormula Term.var φ = φ := by
  induction φ with
  | equal t u | knowledge t u =>
    simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
    simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | neg φ ih => simp only [substituteFormula, ih]
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ => simp only [substituteFormula, hφ, hψ]
  | all φ ih | ex φ ih => simp only [substituteFormula, liftVariables, ih]

/-- A closed universal axiom, read in context one, yields its body with the
bound variable as the free agent variable. -/
private theorem openInstance {A : Sentence → Prop} (B : Formula 1)
    (h : Derivation A (weakenClosed 1 (.all B))) : Nonempty (Derivation A B) := by
  have h' : Derivation A
      (.all (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)) := h
  have r := Derivation.mp (Derivation.logical (A := A)
    (.allInstantiate (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B)
      (Term.var 0))) h'
  have hv : (fun i : Fin 1 => GorbowSubstitution.substitute
      (Fin.cases (Term.var 0) Term.var : Fin 2 → Term 1)
      (liftSubstitute (Fin.elim0 : Fin 0 → Term 1) i)) = Term.var := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  have he : GorbowStandardInstances.instantiate
      (substituteFormula (liftSubstitute (Fin.elim0 : Fin 0 → Term 1)) B) (Term.var 0) = B := by
    unfold GorbowStandardInstances.instantiate
    rw [GorbowFormulaCompositionProof.composition]
    rw [hv, formulaVariables]
  exact ⟨he ▸ r⟩

private theorem liftGuard (c : Nat) :
    weakenClosed 1 (GorbowBooleanTruth.sentenceGuard (Term.numeral c : Term 0)) =
      GorbowBooleanTruth.sentenceGuard (Term.numeral c : Term 1) := by
  simp only [weakenClosed, GorbowBooleanTruth.sentenceGuard, substituteFormula, substHeader,
    List.map_cons, List.map_nil, substNum]

private theorem liftEquation (a b c : Nat) :
    weakenClosed 1 (.equal (Term.numeral c)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral a) (Term.numeral b)) : Sentence) =
      (.equal (Term.numeral c)
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral a) (Term.numeral b)) : Formula 1) := by
  simp only [weakenClosed, GorbowBooleanTruth.binaryCodeTerm, substituteFormula,
    GorbowSubstitution.substitute, substHeader, List.map_cons, List.map_nil, substNum]

/-! ### The universal K2 axiom, opened at the agent -/

/-- Innermost context `[psi, phi, a]` of `GorbowSortedKnowledgeAxioms.distribution`. -/
private def distributionInner : Formula 3 :=
  .imp (GorbowBooleanTruth.sentenceGuard (.var 0))
    (.imp (.conj (.knowledge (.var 2) (.var 1))
      (.knowledge (.var 2) (GorbowBooleanTruth.binaryCodeTerm 0 (.var 1) (.var 0))))
      (.knowledge (.var 2) (.var 0)))

private def distributionMiddle : Formula 2 :=
  .imp (GorbowBooleanTruth.sentenceGuard (.var 0)) (.all distributionInner)

private def distributionBody : Formula 1 := .imp (.agent (.var 0)) (.all distributionMiddle)

private def agentBody (S : Selector) (c : Nat) : Formula 1 :=
  .imp (.agent (.var 0)) (.imp S.val (.knowledge (.var 0) (Term.numeral c)))

private def firstDictionary (cs : Nat) : Fin 2 → Term 1 := Fin.cases (Term.numeral cs) Term.var

private def middleInstance (cs : Nat) : Formula 2 :=
  substituteFormula (liftSubstitute (firstDictionary cs)) distributionInner

private def innerDictionary (cs ct : Nat) : Fin 3 → Term 1 :=
  Fin.cases (Term.numeral ct) (Fin.cases (Term.numeral cs) Term.var)

private theorem innerDictionaryEq (cs ct : Nat) :
    (fun i : Fin 3 => GorbowSubstitution.substitute
      (Fin.cases (Term.numeral ct) Term.var : Fin 2 → Term 1)
      (liftSubstitute (firstDictionary cs) i)) = innerDictionary cs ct := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      exact (congrArg (GorbowSubstitution.substitute
        (Fin.cases (Term.numeral ct) Term.var : Fin 2 → Term 1))
        (substNum (fun k : Fin 1 => (Term.var k.succ : Term 2)) cs)).trans (substNum _ cs)
    | succ k => rfl

private theorem innerInstance (cs ct : Nat) :
    GorbowStandardInstances.instantiate (middleInstance cs) (Term.numeral ct) =
      substituteFormula (innerDictionary cs ct) distributionInner := by
  unfold GorbowStandardInstances.instantiate middleInstance
  rw [GorbowFormulaCompositionProof.composition, innerDictionaryEq]

/-- Selected-agent closure in any theory containing the K2 axiom, the two
literal guards, the implication-code equation and the two everyone-knows
premises as closed axioms. The agent is a free variable throughout. -/
private theorem agentClosure (A : Sentence → Prop) (S : Selector) (cs ct ci : Nat)
    (hD : A GorbowSortedKnowledgeAxioms.distribution)
    (hS : A (GorbowBooleanTruth.sentenceGuard (Term.numeral cs)))
    (hT : A (GorbowBooleanTruth.sentenceGuard (Term.numeral ct)))
    (hE : A (.equal (Term.numeral ci)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))
    (h1 : A (everyone S ci)) (h2 : A (everyone S cs)) :
    Nonempty (Derivation A (everyone S ct)) := by
  obtain ⟨dImp⟩ := openInstance (A := A) (agentBody S ci) (Derivation.axiom (n := 1) _ h1)
  obtain ⟨dAnt⟩ := openInstance (A := A) (agentBody S cs) (Derivation.axiom (n := 1) _ h2)
  obtain ⟨dDist⟩ := openInstance (A := A) distributionBody (Derivation.axiom (n := 1) _ hD)
  have gS : Derivation A (GorbowBooleanTruth.sentenceGuard (Term.numeral cs : Term 1)) := by
    have h := Derivation.axiom (A := A) (n := 1) _ hS
    rw [liftGuard] at h
    exact h
  have gT : Derivation A (GorbowBooleanTruth.sentenceGuard (Term.numeral ct : Term 1)) := by
    have h := Derivation.axiom (A := A) (n := 1) _ hT
    rw [liftGuard] at h
    exact h
  have eqC : Derivation A (.equal (Term.numeral ci : Term 1)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))) := by
    have h := Derivation.axiom (A := A) (n := 1) _ hE
    rw [liftEquation] at h
    exact h
  -- Instantiate the formula-code quantifiers of K2 at the literal numerals.
  have i1 : Derivation A (.imp (.all distributionMiddle)
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral cs : Term 1))
        (.all (middleInstance cs)))) :=
    .logical (.allInstantiate distributionMiddle (Term.numeral cs))
  have hA : Derivation A (.imp (.agent (.var 0))
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral cs : Term 1))
        (.all (middleInstance cs)))) :=
    compose i1 dDist
  have hB : Derivation A (.imp (.agent (.var 0)) (.all (middleInstance cs))) :=
    mpUnder hA (liftK _ gS)
  have i2 : Derivation A (.imp (.all (middleInstance cs))
      (substituteFormula (innerDictionary cs ct) distributionInner)) := by
    rw [← innerInstance cs ct]
    exact .logical (.allInstantiate (middleInstance cs) (Term.numeral ct))
  have hC : Derivation A (.imp (.agent (.var 0))
      (.imp (GorbowBooleanTruth.sentenceGuard (Term.numeral ct : Term 1))
        (.imp (.conj (.knowledge (.var 0) (Term.numeral cs))
          (.knowledge (.var 0)
            (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))
          (.knowledge (.var 0) (Term.numeral ct))))) :=
    compose i2 hB
  have hCD : Derivation A (.imp (.agent (.var 0))
      (.imp (.conj (.knowledge (.var 0) (Term.numeral cs))
        (.knowledge (.var 0)
          (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))
        (.knowledge (.var 0) (Term.numeral ct)))) :=
    mpUnder hC (liftK _ gT)
  -- Move knowledge of the implication numeral to the computed implication code.
  have r1 : Derivation A (.imp (.equal (Term.numeral ci : Term 1)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))
      (.imp (.knowledge (.var 0) (Term.numeral ci))
        (.knowledge (.var 0)
          (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))) :=
    .logical (.equalityReplace (.knowledge (.var 1) (.var 0)) (Term.numeral ci)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))
  have r2 : Derivation A (.imp (.knowledge (.var 0) (Term.numeral ci : Term 1))
      (.knowledge (.var 0)
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))) :=
    .mp r1 eqC
  have hBin : Derivation A (.imp (.agent (.var 0)) (.imp S.val
      (.knowledge (.var 0)
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))) :=
    mpUnder2 (const2 _ _ r2) dImp
  have aI : Derivation A (.imp (.knowledge (.var 0) (Term.numeral cs : Term 1))
      (.imp (.knowledge (.var 0)
        (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))
        (.conj (.knowledge (.var 0) (Term.numeral cs))
          (.knowledge (.var 0)
            (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))))) :=
    .logical (.andIntro _ _)
  have hConj : Derivation A (.imp (.agent (.var 0)) (.imp S.val
      (.conj (.knowledge (.var 0) (Term.numeral cs))
        (.knowledge (.var 0)
          (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))))) :=
    mpUnder2 (mpUnder2 (const2 _ _ aI) dAnt) hBin
  have hFinal : Derivation A (agentBody S ct) :=
    mpUnder2 (weakenUnder S.val hCD) hConj
  exact ⟨.generalize hFinal⟩

/-! ### Discharging the closed premises -/

private theorem dischargeOne {A : Sentence → Prop} {R σ : Sentence}
    (h : Nonempty (Derivation (GorbowClosedDeduction.extend A R) σ)) :
    Nonempty (Derivation A (.imp R σ)) :=
  (GorbowClosedDeductionProof.closedExtension A R σ).mp h

private theorem dischargedClosure (T : Sentence → Prop) (S : Selector) (cs ct ci : Nat)
    (hD : T GorbowSortedKnowledgeAxioms.distribution)
    (hgs : Derivation (n := 0) T (GorbowBooleanTruth.sentenceGuard (Term.numeral cs)))
    (hgt : Derivation (n := 0) T (GorbowBooleanTruth.sentenceGuard (Term.numeral ct)))
    (her : Derivation (n := 0) T (.equal (Term.numeral ci)
      (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct)))) :
    Nonempty (Derivation T (.imp (everyone S ci) (.imp (everyone S cs) (everyone S ct)))) := by
  have core := agentClosure
    (GorbowClosedDeduction.extend (GorbowClosedDeduction.extend (GorbowClosedDeduction.extend
      (GorbowClosedDeduction.extend (GorbowClosedDeduction.extend T
        (GorbowBooleanTruth.sentenceGuard (Term.numeral cs)))
        (GorbowBooleanTruth.sentenceGuard (Term.numeral ct)))
        (.equal (Term.numeral ci)
          (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral cs) (Term.numeral ct))))
      (everyone S ci)) (everyone S cs))
    S cs ct ci
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hD)))))
    (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl)))))
    (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
    (Or.inl (Or.inl (Or.inr rfl)))
    (Or.inl (Or.inr rfl))
    (Or.inr rfl)
  obtain ⟨c0⟩ := dischargeOne (dischargeOne (dischargeOne (dischargeOne (dischargeOne core))))
  exact ⟨.mp (.mp (.mp c0 hgs) hgt) her⟩

private theorem selectedClosure (pF pR : GorbowPRProgram.Program 1) (hcal : Calibrated pF pR)
    (S : Selector) (sigma tau : Sentence) :
    Nonempty (Derivation (Theory pF pR) (selectedDistribution S sigma tau)) := by
  obtain ⟨hgs⟩ := guardCertificate pF pR hcal sigma
  obtain ⟨hgt⟩ := guardCertificate pF pR hcal tau
  obtain ⟨hic⟩ := implicationCertificate pF pR hcal sigma tau
  have hic' : Derivation (Theory pF pR) (.equal
      (GorbowBooleanTruth.binaryCodeTerm 0
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
        (Term.numeral (GorbowSortedSyntaxCode.formulaCode tau)))
      (Term.numeral (GorbowSortedSyntaxCode.formulaCode (Formula.imp sigma tau)))) := hic
  obtain ⟨her⟩ := GorbowTheoryEqualityProof.symmetry (Theory pF pR) _ _ hic'
  exact dischargedClosure (Theory pF pR) S (GorbowSortedSyntaxCode.formulaCode sigma)
    (GorbowSortedSyntaxCode.formulaCode tau)
    (GorbowSortedSyntaxCode.formulaCode (Formula.imp sigma tau)) (Or.inr rfl) hgs hgt her

theorem selectedAgentClosure : GorbowSelectedDistribution.Targets.SelectedAgentClosure :=
  fun pF pR hcal S sigma tau => selectedClosure pF pR hcal S sigma tau

theorem completeSupplier : GorbowSelectedDistribution.Targets.CompleteSupplier := by
  obtain ⟨pF, pR, hcal⟩ := actualPrograms
  obtain ⟨hp, he⟩ := numericAxiomChecker pF pR
  exact ⟨pF, pR, hcal, hp, he, selectedAgentClosure pF pR hcal⟩

theorem fullTarget : GorbowSelectedDistribution.Targets.Target :=
  ⟨actualPrograms, numericAxiomChecker, literalCodingCertificates, selectedAgentClosure,
    completeSupplier⟩

end LogicLineages.ComputabilityKnowledge.GorbowSelectedDistribution.Proof
