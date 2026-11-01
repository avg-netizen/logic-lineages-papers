module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityTargets
public import LogicLineages.ComputabilityKnowledge.GorbowInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowSourceRegistryPaddingProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof

@[expose] public section
/-! Proofs for the checker embedded in the calibrated named registry. The
checker subtree is located at `checkerTag` by actual child-tag and subtree
lookup transport through the padded layout. Numeral certificates are the
named theory's own positive/negative Hilbert certificates; the existential
proof certificate is introduced by `allInstantiate`, the classical branch
rules and `existsDualBackward`; standard semantics uses the actual named
overlay `internalTerm`. The external checked theory is not identified with
the generated base. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution
open List.Vector

/-! ### The augmented dispatcher -/

theorem preservesEvaluation : GorbowNamedInternalProvability.Targets.PreservesEvaluation := by
  intro n p q v
  simp [augment, evaluate, List.Vector.get_ofFn, Fin.cases_zero]

private theorem augmentArgumentTag {n : Nat} (p : Program 1) (q : Program n) :
    GorbowPRChildTags.argumentTag (.projection (0 : Fin 2))
      (Fin.cases p (fun _ => wrapper q) : Fin 2 → Program 1) 1 = 2 + (nodes p).length := by
  unfold GorbowPRChildTags.argumentTag
  simp only [List.ofFn_succ, List.ofFn_zero]
  show 1 + 1 + (nodes p ++ []).length = 2 + (nodes p).length
  rw [List.append_nil]

theorem exactCheckerTag : GorbowNamedInternalProvability.Targets.ExactCheckerTag := by
  intro n p pR q
  have h1 := GorbowSourceRegistryPadding.Proof.functionRoot (augment p q) pR
  have h2 : (nodes (augment p q))[GorbowPRChildTags.argumentTag (.projection (0 : Fin 2))
      (Fin.cases p (fun _ => wrapper q) : Fin 2 → Program 1) 1]? = some ⟨1, wrapper q⟩ := by
    have h := GorbowPRChildTags.Proof.compositionArgument 1 2 (.projection (0 : Fin 2))
      (Fin.cases p (fun _ => wrapper q) : Fin 2 → Program 1) (Fin.succ (0 : Fin 1))
    have h' : (nodes (augment p q))[GorbowPRChildTags.argumentTag (.projection (0 : Fin 2))
        (Fin.cases p (fun _ => wrapper q) : Fin 2 → Program 1) (Fin.succ (0 : Fin 1))]? =
          some ⟨1, wrapper q⟩ := by
      simpa only [augment, Fin.cases_succ] using h
    have hi : Fin.succ (0 : Fin 1) = (1 : Fin 2) := by decide
    simpa only [hi] using h'
  have h3 : (nodes (wrapper q))[1]? = some ⟨n, q⟩ :=
    GorbowPRChildTags.Proof.compositionFunction 1 n q (fun _ => zeroUnary)
  have h12 := GorbowPRSubtree.Proof.lookupTransport 4
    (GorbowSourceRegistryPadding.root (augment p q) pR) _ ⟨1, augment p q⟩ _ ⟨1, wrapper q⟩ h1 h2
  have h123 := GorbowPRSubtree.Proof.lookupTransport 4
    (GorbowSourceRegistryPadding.root (augment p q) pR) _ ⟨1, wrapper q⟩ 1 ⟨n, q⟩ h12 h3
  have htag : GorbowSourceRegistryPadding.functionTag +
      GorbowPRChildTags.argumentTag (.projection (0 : Fin 2))
        (Fin.cases p (fun _ => wrapper q) : Fin 2 → Program 1) 1 + 1 = checkerTag p := by
    rw [augmentArgumentTag]
    unfold GorbowSourceRegistryPadding.functionTag checkerTag
    omega
  rw [← htag]
  exact h123

theorem preservesCalibration : GorbowNamedInternalProvability.Targets.PreservesCalibration := by
  intro n pF pR q h
  exact ⟨fun x => (preservesEvaluation n pF q _).trans (h.1 x), h.2⟩

theorem numeralCertificates : GorbowNamedInternalProvability.Targets.NumeralCertificates := by
  intro n pF pR q v
  exact GorbowNamedDefiningTheory.Proof.internalNumeralCertificates (augment pF q) pR
    (checkerTag pF) n q (exactCheckerTag n pF pR q) v

/-! ### Literal substitution -/

private theorem substituteNumeral {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    substitute σ (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n σ k

private theorem substituteCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (GorbowPRDefiningEquations.call tag args) =
      GorbowPRDefiningEquations.call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

/-- Under the binder, the retained formula-code variable becomes the closed
numeral, shifted into the one-variable context. -/
private theorem liftNumeralSucc (formula : Nat) :
    GorbowFormulaSubstitution.liftSubstitute
      (Fin.cases (Term.numeral formula) Term.var : Fin 1 → Term 0) (1 : Fin 2) =
        Term.numeral formula :=
  substituteNumeral (fun i : Fin 0 => (Term.var i.succ : Term 1)) formula

theorem literalSubstitution : GorbowNamedInternalProvability.Targets.LiteralSubstitution := by
  intro tag formula
  simp only [GorbowStandardInstances.instantiate, provabilityFormula, body,
    GorbowFormulaSubstitution.substituteFormula, substituteCall, substituteNumeral,
    List.Vector.map_cons, List.Vector.map_nil]
  exact congrArg (fun t : Term 1 => Formula.ex (Formula.equal
    (GorbowPRDefiningEquations.call tag (t ::ᵥ Term.var 0 ::ᵥ List.Vector.nil))
    (Term.numeral 1))) (liftNumeralSucc formula)

/-! ### Derived existential introduction -/

/-- The open matrix of `atCode tag formula`; variable0 is the certificate. -/
private def certificateMatrix (tag formula : Nat) : Formula 1 :=
  .equal (GorbowPRDefiningEquations.call tag
    (Term.numeral formula ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)

private theorem refutation (A : Sentence → Prop) (P q : Sentence)
    (hi : Derivation A (.imp P (.neg q))) (hq : Derivation A q) :
    Nonempty (Derivation A (.neg P)) := by
  have hb : GorbowClassicalDerivation.contradictionBranch A (.neg P) (.neg (.neg P)) :=
    Or.inr rfl
  have hn : Derivation (GorbowClassicalDerivation.contradictionBranch A (.neg P))
      (.neg (.neg P)) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
      (Derivation.axiom (A := GorbowClassicalDerivation.contradictionBranch A (.neg P))
        (n := 0) (.neg (.neg P)) hb)
  obtain ⟨hp⟩ := GorbowClassicalDerivation.Proof.doubleNegationElimination _ P hn
  obtain ⟨hi'⟩ := GorbowTheoryProofProof.monotonicity A
    (GorbowClassicalDerivation.contradictionBranch A (.neg P))
    (fun _ hs => Or.inl hs) 0 _ ⟨hi⟩
  obtain ⟨hq'⟩ := GorbowTheoryProofProof.monotonicity A
    (GorbowClassicalDerivation.contradictionBranch A (.neg P))
    (fun _ hs => Or.inl hs) 0 _ ⟨hq⟩
  obtain ⟨hc⟩ := GorbowClassicalDerivation.Proof.explosion _ q (.neg P) hq' (.mp hi' hp)
  exact GorbowClassicalDerivation.Proof.closedReductio A (.neg P) hc

private theorem existsIntroduction (A : Sentence → Prop) (a : Formula 1) (t : Term 0)
    (h : Derivation A (GorbowStandardInstances.instantiate a t)) :
    Nonempty (Derivation A (.ex a)) := by
  have hi : Derivation A
      (.imp (.all (.neg a)) (.neg (GorbowStandardInstances.instantiate a t))) :=
    .logical (.allInstantiate (.neg a) t)
  obtain ⟨hn⟩ := refutation A (.all (.neg a)) (GorbowStandardInstances.instantiate a t) hi h
  exact ⟨.mp (.logical (.existsDualBackward a)) hn⟩

private theorem instantiateMatrix (tag formula certificate : Nat) :
    GorbowStandardInstances.instantiate (certificateMatrix tag formula)
        (Term.numeral certificate) =
      .equal (GorbowPRDefiningEquations.call tag (GorbowPRNumeralCalculation.numeralArguments
        (GorbowInternalProvability.arguments formula certificate))) (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate, certificateMatrix,
    GorbowFormulaSubstitution.substituteFormula, substituteCall, substituteNumeral,
    List.Vector.map_cons, List.Vector.map_nil]
  rfl

/-- An actual existential proof certificate in the augmented named base. -/
private theorem namedCertificate (pF pR : Program 1) (q : Program 2) (formula certificate : Nat)
    (he : evaluate q (GorbowInternalProvability.arguments formula certificate) = 1) :
    Nonempty (Derivation (GorbowNamedDefiningTheory.Theory (augment pF q) pR)
      (atCode (checkerTag pF) formula)) := by
  obtain ⟨d⟩ := (numeralCertificates 2 pF pR q
    (GorbowInternalProvability.arguments formula certificate)).1
  rw [he] at d
  have d' : Derivation (GorbowNamedDefiningTheory.Theory (augment pF q) pR)
      (GorbowStandardInstances.instantiate (certificateMatrix (checkerTag pF) formula)
        (Term.numeral certificate)) := by
    rw [instantiateMatrix]
    exact d
  exact existsIntroduction _ (certificateMatrix (checkerTag pF) formula)
    (Term.numeral certificate) d'

/-! ### Checker values -/

private theorem certificateValue (axCheck : List Nat → Bool) (q : Program 2)
    (hq : GorbowInternalProvability.Represents axCheck q) (formula x : Nat) :
    evaluate q (GorbowInternalProvability.arguments formula x) = 1 ↔
      GorbowTheoryNumericCertificate.check axCheck 0 formula x = true := by
  rw [hq formula x]
  cases h : GorbowTheoryNumericCertificate.check axCheck 0 formula x <;>
    simp [GorbowInternalProvability.checkerValue, h]

/-! ### Named internalization -/

theorem namedInternalization : GorbowNamedInternalProvability.Targets.NamedInternalization := by
  intro axCheck ha
  obtain ⟨_, _, pF, pR, hF, hR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  obtain ⟨q, hq⟩ := GorbowInternalProvability.Proof.checkerProgram axCheck ha
  refine ⟨pF, pR, q, preservesCalibration 2 pF pR q ⟨hF, hR⟩, hq, fun sigma hd => ?_⟩
  obtain ⟨c, hc⟩ := (GorbowTheoryNumericCertificateProof.proofEquivalence axCheck 0
    (GorbowSortedSyntaxCode.formulaCode sigma)).mpr ⟨sigma, rfl, hd⟩
  exact namedCertificate pF pR q _ c
    ((certificateValue axCheck q hq (GorbowSortedSyntaxCode.formulaCode sigma) c).mpr hc)

/-! ### Exact standard semantics in the named overlay -/

private theorem realizeCall (pF pR : Program 1) (q : Program 2) (I : Interpretation)
    (formula x : Nat) :
    (GorbowPRDefiningEquations.call (checkerTag pF)
      (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil : List.Vector (Term 1) 2)).realize
        (GorbowNamedRegistryInterpretation.interpretation (augment pF q) pR I)
        (Fin.cases x Fin.elim0) =
      evaluate q (GorbowInternalProvability.arguments formula x) := by
  rw [GorbowNamedRegistryInterpretation.Proof.internalTerm 1 (augment pF q) pR (checkerTag pF) 2 q
    (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil) I (Fin.cases x Fin.elim0)
    (exactCheckerTag 2 pF pR q)]
  simp only [List.Vector.map_cons, List.Vector.map_nil, numeral_realize,
    GorbowInternalProvability.arguments] <;> rfl

private theorem realizeAtCode (pF pR : Program 1) (q : Program 2) (I : Interpretation)
    (formula : Nat) :
    Formula.realize (GorbowNamedRegistryInterpretation.interpretation (augment pF q) pR I)
        Fin.elim0 (atCode (checkerTag pF) formula) ↔
      ∃ x, evaluate q (GorbowInternalProvability.arguments formula x) = 1 := by
  apply exists_congr
  intro x
  show (GorbowPRDefiningEquations.call (checkerTag pF)
      (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil : List.Vector (Term 1) 2)).realize
        (GorbowNamedRegistryInterpretation.interpretation (augment pF q) pR I)
        (Fin.cases x Fin.elim0) =
    (Term.numeral 1 : Term 1).realize
      (GorbowNamedRegistryInterpretation.interpretation (augment pF q) pR I)
      (Fin.cases x Fin.elim0) ↔ _
  rw [realizeCall, numeral_realize]

theorem exactStandardSemantics :
    GorbowNamedInternalProvability.Targets.ExactStandardSemantics := by
  intro axCheck q hq pF pR I formula
  rw [realizeAtCode]
  have hcert : (∃ x, evaluate q (GorbowInternalProvability.arguments formula x) = 1) ↔
      ∃ x, GorbowTheoryNumericCertificate.check axCheck 0 formula x = true :=
    exists_congr fun x => certificateValue axCheck q hq formula x
  rw [hcert]
  exact GorbowTheoryNumericCertificateProof.proofEquivalence axCheck 0 formula

theorem fullTarget : GorbowNamedInternalProvability.Targets.Target :=
  ⟨preservesEvaluation, exactCheckerTag, preservesCalibration, numeralCertificates,
    literalSubstitution, namedInternalization, exactStandardSemantics⟩

end LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvability.Proof
