module

public import LogicLineages.ComputabilityKnowledge.GorbowInternalProvabilityTargets
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRCallCongruenceProof
public import LogicLineages.ComputabilityKnowledge.GorbowHeaderSubstitutionProof
public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationProof

@[expose] public section
/-! Proofs for the internal provability interface. The checker program is
compiled from the existing uniform primitive-recursive numeric checker; the
numeral certificates are actual Hilbert derivations in the named PR defining
theory, with existential introduction derived from `allInstantiate`, the
classical branch rules and `existsDualBackward`. Registry tag0 is located by
`rootTag`, not by an oracle. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPRDefiningEquations
open GorbowSubstitution List.Vector

/-! ### Checker program -/

private theorem checkerPrimitive (axCheck : List Nat → Bool) (ha : Primrec axCheck) :
    Primrec (fun v : List.Vector Nat 2 => checkerValue axCheck v.head v.tail.head) := by
  have hu := GorbowTheoryNumericCertificateProof.uniformProgram axCheck ha
  have hargs : Primrec (fun v : List.Vector Nat 2 => ((0 : Nat), v.head, v.tail.head)) :=
    Primrec.pair (Primrec.const 0)
      (Primrec.pair Primrec.vector_head (Primrec.vector_head.comp Primrec.vector_tail))
  have hc : Primrec (fun v : List.Vector Nat 2 =>
      GorbowTheoryNumericCertificate.check axCheck 0 v.head v.tail.head) :=
    hu.comp hargs
  exact (Primrec.cond hc (Primrec.const 1) (Primrec.const 0)).of_eq fun v => by
    cases h : GorbowTheoryNumericCertificate.check axCheck 0 v.head v.tail.head <;>
      simp [checkerValue, h]

theorem checkerProgram : Targets.CheckerProgram := by
  intro axCheck ha
  obtain ⟨p, hp⟩ :=
    GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ (checkerPrimitive axCheck ha)
  exact ⟨p, fun formula certificate => hp (arguments formula certificate)⟩

/-! ### Literal substitution -/

private theorem substituteNumeral {m n : Nat} (σ : Fin m → Term n) (k : Nat) :
    substitute σ (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n σ k

private theorem substituteCall {ctx out arity : Nat} (tag : Nat)
    (args : List.Vector (Term ctx) arity) (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

/-- Under the binder, the retained formula-code variable becomes the closed
numeral, shifted into the one-variable context. -/
private theorem liftNumeralSucc (formula : Nat) :
    GorbowFormulaSubstitution.liftSubstitute
      (Fin.cases (Term.numeral formula) Term.var : Fin 1 → Term 0) (1 : Fin 2) =
        Term.numeral formula :=
  substituteNumeral (fun i : Fin 0 => (Term.var i.succ : Term 1)) formula

theorem literalSubstitution : Targets.LiteralSubstitution := by
  intro formula
  simp only [GorbowStandardInstances.instantiate, provabilityFormula, body,
    GorbowFormulaSubstitution.substituteFormula, substituteCall, substituteNumeral,
    List.Vector.map_cons, List.Vector.map_nil]
  exact congrArg (fun t : Term 1 => Formula.ex (Formula.equal
    (call 0 (t ::ᵥ Term.var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)))
    (liftNumeralSucc formula)

/-! ### Derived existential introduction -/

/-- The open matrix of `atCode formula`; variable0 is the certificate. -/
private def certificateMatrix (formula : Nat) : Formula 1 :=
  .equal (call 0 (Term.numeral formula ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)

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

/-! ### Numeral certification -/

private theorem instantiateMatrix (formula certificate : Nat) :
    GorbowStandardInstances.instantiate (certificateMatrix formula)
        (Term.numeral certificate) =
      .equal (call 0 (GorbowPRNumeralCalculation.numeralArguments
        (arguments formula certificate))) (Term.numeral 1) := by
  simp only [GorbowStandardInstances.instantiate, certificateMatrix,
    GorbowFormulaSubstitution.substituteFormula, substituteCall, substituteNumeral,
    List.Vector.map_cons, List.Vector.map_nil]
  rfl

theorem numeralCertification : Targets.NumeralCertification := by
  intro p formula certificate he
  obtain ⟨d⟩ := GorbowPRNumeralCalculation.Proof.numeralCalculation 2 p 0 2 p
    (GorbowPRRegistry.Proof.rootTag 2 p) (arguments formula certificate)
  rw [he] at d
  have d' : Derivation (GorbowPRNumeralCalculation.Theory p)
      (GorbowStandardInstances.instantiate (certificateMatrix formula)
        (Term.numeral certificate)) := by
    rw [instantiateMatrix]
    exact d
  exact existsIntroduction _ (certificateMatrix formula) (Term.numeral certificate) d'

/-! ### Exact standard semantics -/

private theorem realizeCall (p : Program 2) (I : Interpretation) (formula x : Nat) :
    (call 0 (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil :
        List.Vector (Term 1) 2)).realize (interpretation p I) (Fin.cases x Fin.elim0) =
      evaluate p (arguments formula x) := by
  rw [GorbowPRDefiningEquations.Proof.termCalibration 1 2 p 0 2 p
    (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil) I (Fin.cases x Fin.elim0)
    (GorbowPRRegistry.Proof.rootTag 2 p)]
  simp only [List.Vector.map_cons, List.Vector.map_nil, numeral_realize, arguments] <;> rfl

private theorem realizeAtCode (p : Program 2) (I : Interpretation) (formula : Nat) :
    Formula.realize (interpretation p I) Fin.elim0 (atCode formula) ↔
      ∃ x, evaluate p (arguments formula x) = 1 := by
  apply exists_congr
  intro x
  show (call 0 (Term.numeral formula ::ᵥ Term.var 0 ::ᵥ List.Vector.nil :
      List.Vector (Term 1) 2)).realize (interpretation p I) (Fin.cases x Fin.elim0) =
    (Term.numeral 1 : Term 1).realize (interpretation p I) (Fin.cases x Fin.elim0) ↔ _
  rw [realizeCall, numeral_realize]

private theorem certificateValue (axCheck : List Nat → Bool) (p : Program 2)
    (hp : Represents axCheck p) (formula x : Nat) :
    evaluate p (arguments formula x) = 1 ↔
      GorbowTheoryNumericCertificate.check axCheck 0 formula x = true := by
  rw [hp formula x]
  cases h : GorbowTheoryNumericCertificate.check axCheck 0 formula x <;>
    simp [checkerValue, h]

theorem exactStandardSemantics : Targets.ExactStandardSemantics := by
  intro axCheck p hp I formula
  rw [realizeAtCode]
  have hcert : (∃ x, evaluate p (arguments formula x) = 1) ↔
      ∃ x, GorbowTheoryNumericCertificate.check axCheck 0 formula x = true :=
    exists_congr fun x => certificateValue axCheck p hp formula x
  rw [hcert]
  exact GorbowTheoryNumericCertificateProof.proofEquivalence axCheck 0 formula

/-! ### Internal certification -/

theorem internalCertification : Targets.InternalCertification := by
  intro axCheck ha
  obtain ⟨p, hp⟩ := checkerProgram axCheck ha
  refine ⟨p, hp, fun phi hd => ?_⟩
  obtain ⟨c, hc⟩ := (GorbowTheoryNumericCertificateProof.proofEquivalence axCheck 0
    (GorbowSortedSyntaxCode.formulaCode phi)).mpr ⟨phi, rfl, hd⟩
  exact numeralCertification p _ c
    ((certificateValue axCheck p hp (GorbowSortedSyntaxCode.formulaCode phi) c).mpr hc)

theorem fullTarget : Targets.Target :=
  ⟨checkerProgram, literalSubstitution, numeralCertification, exactStandardSemantics,
    internalCertification⟩

end LogicLineages.ComputabilityKnowledge.GorbowInternalProvability.Proof
