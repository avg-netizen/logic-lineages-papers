module

public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeTargets
public import LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplicationProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof

@[expose] public section
/-! One retained-parameter common-knowledge formula and its closed Hilbert
fixed-point equations in the actual D. Exact AST computation of the template
and literal-body instances uses generic substitution identity, numeral, call
and composition lemmas; the R021 arity-two program is located as a real
subtree of the enriched source registry, its numeral equation is derived in the
named finite defining theory and carried into S and D, and Hilbert equality
substitution gives the biconditionals. No fixed-point axiom, semantic
completeness, internal CBE, original Base or HB assumption is used. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.Proof
open GorbowSyntax GorbowPRProgram GorbowSortedSyntaxCode

/-! ### Generic substitution facts -/

private theorem liftVar (n : Nat) :
    GorbowFormulaSubstitution.liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaIdentity {n : Nat} (φ : Formula n) :
    GorbowFormulaSubstitution.substituteFormula Term.var φ = φ := by
  induction φ <;> simp only [GorbowFormulaSubstitution.substituteFormula,
    GorbowSubstitution.substitute_variables, liftVar, *]

private theorem selectorLift {m : Nat} (X : Fin m → Term 0) (B : Formula 1) :
    GorbowFormulaSubstitution.substituteFormula (GorbowFormulaSubstitution.liftSubstitute X)
      (GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term (m+1))) B) = B := by
  have he : (fun i : Fin 1 => GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute X)
      ((fun _ : Fin 1 => (Term.var 0 : Term (m+1))) i)) = (Term.var : Fin 1 → Term 1) := by
    funext i
    exact congrArg Term.var (Subsingleton.elim (0 : Fin 1) i)
  exact (GorbowFormulaCompositionProof.composition 1 (m+1) (0+1) B _ _).trans
    ((congrArg (fun d => GorbowFormulaSubstitution.substituteFormula d B) he).trans (formulaIdentity B))

private theorem weakenCancel {n : Nat} (τ : Fin n → Term 0) (ε : Sentence) :
    GorbowFormulaSubstitution.substituteFormula τ (GorbowTheoryProof.weakenClosed n ε) = ε := by
  have he : (fun i : Fin 0 => GorbowSubstitution.substitute τ ((Fin.elim0 : Fin 0 → Term n) i)) =
      (Term.var : Fin 0 → Term 0) := by
    funext i; exact Fin.elim0 i
  exact (GorbowFormulaCompositionProof.composition 0 n 0 ε (Fin.elim0 : Fin 0 → Term n) τ).trans
    ((congrArg (fun d => GorbowFormulaSubstitution.substituteFormula d ε) he).trans (formulaIdentity ε))

private theorem liftNumeral {m : Nat} (cd : Fin m → Term 0) (i : Fin m) (a : Nat)
    (h : cd i = Term.numeral a) :
    GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute cd) (Term.var i.succ) =
      Term.numeral a := by
  change GorbowFormulaSubstitution.renameTerm Fin.succ (cd i) = _
  rw [h]
  exact GorbowHeaderSubstitutionProof.numerals _ _ _ a

private theorem vectorPair {α β : Type} {f : α → β} {x y : α} {a b : β} (hx : f x = a) (hy : f y = b) :
    (x ::ᵥ y ::ᵥ List.Vector.nil).map f = a ::ᵥ b ::ᵥ List.Vector.nil := by
  subst hx; subst hy; rfl

private theorem callNumerals {k n : Nat} (ρ : Fin k → Term n) (tag a b : Nat) :
    GorbowSubstitution.substitute ρ (GorbowPRDefiningEquations.call tag
      ((Term.numeral a : Term k) ::ᵥ (Term.numeral b : Term k) ::ᵥ List.Vector.nil)) =
    GorbowPRDefiningEquations.call tag
      ((Term.numeral a : Term n) ::ᵥ (Term.numeral b : Term n) ::ᵥ List.Vector.nil) :=
  (GorbowPRCallCongruence.Proof.callSubstitution k n 2 tag _ ρ).trans
    (congrArg (GorbowPRDefiningEquations.call tag)
      (vectorPair (f := GorbowSubstitution.substitute ρ)
        (GorbowHeaderSubstitutionProof.numerals k n ρ a)
        (GorbowHeaderSubstitutionProof.numerals k n ρ b)))

/-! ### The retained parameter -/

private theorem commonShape (tag : Nat) (A : Selector) :
    ∃ (S : Formula 2) (R : Formula 1), common tag A =
      .conj (.all (.imp (.agent (.var 0)) (.imp S (.knowledge (.var 0) (.var 1))))) R :=
  ⟨_, _, rfl⟩

private theorem orLeft {a b : Bool} (h : a = true) : (a || b) = true := by
  subst h; rfl

private theorem orRight {a b : Bool} (h : b = true) : (a || b) = true := by
  subst h; cases a <;> rfl

theorem retainedParameter : GorbowUniformCommonKnowledge.Targets.RetainedParameter := by
  intro tag A
  obtain ⟨S, R, h⟩ := commonShape tag A
  rw [h]
  exact orLeft (orRight (orRight
    (rfl : (Formula.knowledge (.var 0) (.var 1) : Formula 2).uses (Fin.succ (0 : Fin 1)) = true)))

/-! ### Exact template and literal-body instances -/

private theorem templateForm (tag : Nat) (A : Selector) (cd : Fin 2 → Term 0) (a u : Nat)
    (h0 : cd 0 = Term.numeral a) (h1 : cd 1 = Term.numeral u) :
    GorbowFormulaSubstitution.substituteFormula cd (template tag A) =
      .conj (everyone A u)
        (.all (.imp (.agent (.var 0)) (.imp A.val (.knowledge (.var 0)
          (GorbowPRDefiningEquations.call tag
            (Term.numeral a ::ᵥ Term.numeral u ::ᵥ List.Vector.nil)))))) := by
  have hs : GorbowFormulaSubstitution.substituteFormula (GorbowFormulaSubstitution.liftSubstitute cd)
      (GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term 3)) A.val) =
      A.val :=
    selectorLift cd A.val
  have e1 : GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute cd)
      (Term.var 1 : Term 3) = Term.numeral a :=
    liftNumeral cd 0 a h0
  have e2 : GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute cd)
      (Term.var 2 : Term 3) = Term.numeral u :=
    liftNumeral cd 1 u h1
  have ec : GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute cd)
      (GorbowPRDefiningEquations.call tag ((Term.var 1 : Term 3) ::ᵥ Term.var 2 ::ᵥ List.Vector.nil)) =
      GorbowPRDefiningEquations.call tag (Term.numeral a ::ᵥ Term.numeral u ::ᵥ List.Vector.nil) :=
    (GorbowPRCallCongruence.Proof.callSubstitution _ _ 2 tag _ _).trans
      (congrArg (GorbowPRDefiningEquations.call tag)
        (vectorPair (f := GorbowSubstitution.substitute (GorbowFormulaSubstitution.liftSubstitute cd))
          e1 e2))
  exact congrArg₂ Formula.conj
    (congrArg Formula.all (congrArg₂ Formula.imp rfl
      (congrArg₂ Formula.imp hs (congrArg₂ Formula.knowledge rfl e2))))
    (congrArg Formula.all (congrArg₂ Formula.imp rfl
      (congrArg₂ Formula.imp hs (congrArg₂ Formula.knowledge rfl ec))))

private theorem literalForm (tag : Nat) (A : Selector) (sigma : Sentence) :
    GorbowStandardInstances.instantiate (literalBody A sigma) (closedCall tag A sigma) =
      .conj (everyone A (formulaCode sigma))
        (.all (.imp (.agent (.var 0)) (.imp A.val (.knowledge (.var 0)
          (GorbowPRDefiningEquations.call tag
            (Term.numeral (formulaCode (template tag A)) ::ᵥ Term.numeral (formulaCode sigma) ::ᵥ
              List.Vector.nil)))))) := by
  have hw := weakenCancel (Fin.cases (closedCall tag A sigma) Term.var : Fin 1 → Term 0)
    (everyone A (formulaCode sigma))
  have hs : GorbowFormulaSubstitution.substituteFormula
      (GorbowFormulaSubstitution.liftSubstitute
        (Fin.cases (closedCall tag A sigma) Term.var : Fin 1 → Term 0))
      (GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term 2)) A.val) =
      A.val :=
    selectorLift _ A.val
  have el : GorbowSubstitution.substitute
      (GorbowFormulaSubstitution.liftSubstitute
        (Fin.cases (closedCall tag A sigma) Term.var : Fin 1 → Term 0))
      (Term.var 1 : Term 2) =
      GorbowPRDefiningEquations.call tag
        (Term.numeral (formulaCode (template tag A)) ::ᵥ Term.numeral (formulaCode sigma) ::ᵥ
          List.Vector.nil) := by
    change GorbowFormulaSubstitution.renameTerm Fin.succ (closedCall tag A sigma) = _
    exact callNumerals _ tag (formulaCode (template tag A)) (formulaCode sigma)
  exact congrArg₂ Formula.conj hw
    (congrArg Formula.all (congrArg₂ Formula.imp rfl
      (congrArg₂ Formula.imp hs (congrArg₂ Formula.knowledge rfl el))))

theorem literalBodyRewrite : GorbowUniformCommonKnowledge.Targets.LiteralBodyRewrite := by
  intro tag A sigma
  have h1 : closedInstance tag A sigma =
      GorbowParameterSelfApplication.closedSelf (template tag A) (formulaCode sigma) :=
    GorbowParameterSelfApplication.Proof.literalCommutation (template tag A) (formulaCode sigma)
  have h2 := templateForm tag A
    (GorbowParameterSelfApplication.closedDictionary (template tag A) (formulaCode sigma))
    (formulaCode (template tag A)) (formulaCode sigma) rfl rfl
  exact h1.trans (h2.trans (literalForm tag A sigma).symm)

theorem numeralBody : GorbowUniformCommonKnowledge.Targets.NumeralBody := by
  intro A sigma out
  have hw := weakenCancel (Fin.cases (Term.numeral out) Term.var : Fin 1 → Term 0)
    (everyone A (formulaCode sigma))
  have hs : GorbowFormulaSubstitution.substituteFormula
      (GorbowFormulaSubstitution.liftSubstitute
        (Fin.cases (Term.numeral out) Term.var : Fin 1 → Term 0))
      (GorbowFormulaSubstitution.substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term 2)) A.val) =
      A.val :=
    selectorLift _ A.val
  have el : GorbowSubstitution.substitute
      (GorbowFormulaSubstitution.liftSubstitute
        (Fin.cases (Term.numeral out) Term.var : Fin 1 → Term 0))
      (Term.var 1 : Term 2) = Term.numeral out :=
    liftNumeral (Fin.cases (Term.numeral out) Term.var : Fin 1 → Term 0) 0 out rfl
  exact congrArg₂ Formula.conj hw
    (congrArg Formula.all (congrArg₂ Formula.imp rfl
      (congrArg₂ Formula.imp hs (congrArg₂ Formula.knowledge rfl el))))

/-! ### Installing the arity-two program in the actual registry -/

private theorem installedOccurs (pF0 pR : Program 1) (p : Program 2) (q : Program 5) :
    GorbowPRRegistry.Occurs ⟨2, p⟩ (GorbowSourceRegistryPadding.root
      (GorbowPublishedDCB.augmented (GorbowNamedInternalProvability.augment pF0 p) q) pR) := by
  have h1 : GorbowPRRegistry.Occurs ⟨2, p⟩ (GorbowNamedInternalProvability.wrapper p) :=
    .compositionFunction _ _ (.here p rfl)
  have h2 : GorbowPRRegistry.Occurs ⟨2, p⟩ (GorbowNamedInternalProvability.augment pF0 p) :=
    .compositionArgument _ _ (1 : Fin 2) h1
  have h3 : GorbowPRRegistry.Occurs ⟨2, p⟩
      (GorbowPublishedDCB.augmented (GorbowNamedInternalProvability.augment pF0 p) q) :=
    .compositionArgument _ _ (0 : Fin 2) h2
  have h4 : GorbowPRRegistry.Occurs ⟨2, p⟩ (GorbowSourceRegistryPadding.wrapper
      (GorbowPublishedDCB.augmented (GorbowNamedInternalProvability.augment pF0 p) q)) :=
    .compositionFunction _ _ h3
  exact .compositionArgument _ _ (3 : Fin 5) h4

theorem enrichedParameters : GorbowUniformCommonKnowledge.Targets.EnrichedParameters := by
  obtain ⟨p, hp⟩ := GorbowParameterSelfApplication.Proof.programWitness
  obtain ⟨_, _, pF0, pR, hF, hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  obtain ⟨q, hq⟩ := GorbowEnumeratedProvability.Proof.fixedUniversalProgram
  have hcal := GorbowNamedInternalProvability.Proof.preservesCalibration 2 pF0 pR p ⟨hF, hR⟩
  obtain ⟨c, hc⟩ := (GorbowPublishedDCB.Proof.finiteSPresentation
    (GorbowNamedInternalProvability.augment pF0 p) pR q).2
  obtain ⟨tag, _, htag⟩ :=
    (GorbowPRRegistry.Proof.taggedCoverage _ _ _).mp (installedOccurs pF0 pR p q)
  exact ⟨GorbowNamedInternalProvability.augment pF0 p, pR, q, c, tag, p, ⟨hcal, hq, hc⟩, hp, htag⟩

/-! ### The closed code equation in actual D -/

private theorem codeValue (p : Program 2) (hp : CodeProgram p) (tag : Nat) (A : Selector)
    (sigma : Sentence) :
    evaluate p (formulaCode (template tag A) ::ᵥ formulaCode sigma ::ᵥ List.Vector.nil) =
      formulaCode (closedInstance tag A sigma) := by
  have h1 := hp (formulaCode (template tag A)) (formulaCode sigma)
  have h2 := GorbowParameterSelfApplication.Proof.numericCalibration (template tag A) (formulaCode sigma)
  have h3 : closedInstance tag A sigma =
      GorbowParameterSelfApplication.closedSelf (template tag A) (formulaCode sigma) :=
    GorbowParameterSelfApplication.Proof.literalCommutation (template tag A) (formulaCode sigma)
  rw [h1, h2, h3, Option.getD_some]

private theorem theoryInD (pF pR : Program 1) (q : Program 5) (c : Nat.Partrec.Code) :
    ∀ σ, GorbowNamedDefiningTheory.Theory (GorbowPublishedDCB.augmented pF q) pR σ →
      GorbowPublishedDCB.D pF pR q c σ :=
  fun _ h => Or.inl (List.mem_append_left _ h)

theorem codeEquation : GorbowUniformCommonKnowledge.Targets.CodeEquation := by
  intro pF pR q c tag p _ hp hinst A sigma
  obtain ⟨d⟩ := (GorbowNamedDefiningTheory.Proof.internalNumeralCertificates
    (GorbowPublishedDCB.augmented pF q) pR tag 2 p hinst
    (formulaCode (template tag A) ::ᵥ formulaCode sigma ::ᵥ List.Vector.nil)).1
  have h := GorbowTheoryProofProof.monotonicity _ _ (theoryInD pF pR q c) 0 _ ⟨d⟩
  rw [codeValue p hp tag A sigma] at h
  exact h

/-! ### Closed Hilbert fixed-point equations -/

theorem closedFixedPoint : GorbowUniformCommonKnowledge.Targets.ClosedFixedPoint := by
  intro pF pR q c tag p hA hp hinst A sigma
  obtain ⟨d⟩ := codeEquation pF pR q c tag p hA hp hinst A sigma
  have h := GorbowTheoryEqualityProof.formulaEquivalence (GorbowPublishedDCB.D pF pR q c)
    (literalBody A sigma) _ _ d
  rw [← literalBodyRewrite tag A sigma, numeralBody A sigma] at h
  exact h

theorem concreteCommonKnowledge : GorbowUniformCommonKnowledge.Targets.ConcreteCommonKnowledge := by
  obtain ⟨pF, pR, q, c, tag, p, hA, hp, hinst⟩ := enrichedParameters
  exact ⟨pF, pR, q, c, tag, hA, closedFixedPoint pF pR q c tag p hA hp hinst⟩

theorem fullTarget : GorbowUniformCommonKnowledge.Targets.Target :=
  ⟨retainedParameter, literalBodyRewrite, numeralBody, enrichedParameters, codeEquation,
    closedFixedPoint, concreteCommonKnowledge⟩

end LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledge.Proof
