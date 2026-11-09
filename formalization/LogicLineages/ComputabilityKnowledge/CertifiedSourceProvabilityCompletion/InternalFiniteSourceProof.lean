module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSourceTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LogicalSupportProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof
open GorbowFormulaSubstitution GorbowSortedSyntaxCode List.Vector

private theorem substNum {m n : Nat} (sigma : Fin m → Term n) (k : Nat) :
    GorbowSubstitution.substitute sigma (Term.numeral k) = Term.numeral k :=
  GorbowHeaderSubstitutionProof.numerals m n sigma k

private theorem substCall {m n arity : Nat} (sigma : Fin m → Term n) (tag : Nat)
    (args : List.Vector (Term m) arity) :
    GorbowSubstitution.substitute sigma (GorbowPRDefiningEquations.call tag args) =
      GorbowPRDefiningEquations.call tag (args.map (GorbowSubstitution.substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution m n arity tag args sigma

private theorem liftedNumeral (k : Nat) :
    renameTerm (Fin.succ : Fin 0 → Fin 1) (Term.numeral k) = Term.numeral k := by
  unfold renameTerm
  exact substNum _ k

private theorem liftVariables (n : Nat) :
    liftSubstitute (Term.var : Fin n → Term n) = Term.var := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

private theorem formulaVariables {n : Nat} (phi : Formula n) :
    substituteFormula Term.var phi = phi := by
  induction phi with
  | equal t u | knowledge t u =>
      simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      simp only [substituteFormula, GorbowSubstitution.substitute_variables]
  | neg phi ih => simp only [substituteFormula, ih]
  | imp phi psi hp hq | conj phi psi hp hq | disj phi psi hp hq =>
      simp only [substituteFormula, hp, hq]
  | all phi ih | ex phi ih => simp only [substituteFormula, liftVariables, ih]

private def closedAt (phi : Formula 1) (code : Nat) : Sentence :=
  substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 0)) phi

private def replacementMatrix (phi : Formula 1) : Formula 2 :=
  substituteFormula (fun _ : Fin 1 => (Term.var 0 : Term 2)) phi

private theorem instantiateReplacement (phi : Formula 1) (t : Term 1) :
    GorbowStandardInstances.instantiate (replacementMatrix phi) t =
      substituteFormula (fun _ : Fin 1 => t) phi := by
  unfold GorbowStandardInstances.instantiate replacementMatrix
  rw [GorbowFormulaCompositionProof.composition]
  rfl

private theorem replacementVariable (phi : Formula 1) :
    GorbowStandardInstances.instantiate (replacementMatrix phi) (Term.var 0 : Term 1) = phi := by
  rw [instantiateReplacement]
  have h : (fun _ : Fin 1 => (Term.var 0 : Term 1)) = Term.var := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [h, formulaVariables]

private theorem liftClosedAt (phi : Formula 1) (code : Nat) :
    weakenClosed 1 (closedAt phi code) =
      substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 1)) phi := by
  unfold weakenClosed closedAt
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  exact substNum _ code

private theorem numeralCase (T : Sentence → Prop) (phi : Formula 1) (code : Nat)
    (h : Nonempty (Derivation T (closedAt phi code))) :
    Nonempty (Derivation T (.imp (.equal (Term.numeral code : Term 1) (.var 0)) phi)) := by
  obtain ⟨hl⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ h 1
  rw [liftClosedAt] at hl
  have hr : Derivation T (.imp (.equal (Term.numeral code : Term 1) (.var 0))
      (.imp (substituteFormula (fun _ : Fin 1 => (Term.numeral code : Term 1)) phi) phi)) := by
    have d := Derivation.logical (A := T)
      (.equalityReplace (replacementMatrix phi) (Term.numeral code : Term 1) (.var 0))
    rw [GorbowPACore.logicalFormula, instantiateReplacement phi (Term.numeral code),
      replacementVariable] at d
    exact d
  exact ⟨Hilbert.mpUnder hr (Hilbert.lift _ hl)⟩

private theorem finiteCases (T : Sentence → Prop) (phi : Formula 1) :
    ∀ sentences : List Sentence,
    (∀ sigma ∈ sentences, Nonempty (Derivation T (closedAt phi (formulaCode sigma)))) →
    Nonempty (Derivation T (.imp (codeList sentences) phi)) := by
  intro sentences
  induction sentences with
  | nil =>
      intro _
      obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals T 0 1 (by decide)
      obtain ⟨hn1⟩ := GorbowDerivationSubstitution.Proof.closedLifting T _ ⟨hn⟩ 1
      have hb : Hilbert.Local T 1 [codeList []] (codeList []) := .hypothesis List.mem_cons_self
      have hp : Hilbert.Local T 1 [codeList []] phi := Hilbert.Local.explosion phi hb (.base hn1)
      exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hp)⟩
  | cons sigma rest ih =>
      intro h
      obtain ⟨head⟩ := numeralCase T phi (formulaCode sigma) (h sigma List.mem_cons_self)
      obtain ⟨tail⟩ := ih (fun tau htau => h tau (List.mem_cons_of_mem _ htau))
      exact ⟨.mp (.mp (.logical (.orElim _ _ _)) head) tail⟩

private def certificateMatrix (pF : Program 1) (c : Code) (fuel code : Nat) : Formula 1 :=
  .equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ Term.numeral fuel ::ᵥ Term.numeral 0 ::ᵥ
      Term.numeral code ::ᵥ .var 0 ::ᵥ nil)) (Term.numeral 1)

private theorem closedFixedFuel (pF : Program 1) (c : Code) (fuel code : Nat) :
    closedAt (fixedFuelProvability pF c fuel) code = .ex (certificateMatrix pF c fuel code) := by
  simp only [closedAt, fixedFuelProvability, substituteFormula, substCall, substNum,
    List.Vector.map_cons, List.Vector.map_nil, GorbowSubstitution.substitute,
    liftSubstitute, liftedNumeral]
  rfl

private theorem instantiateCertificate (pF : Program 1) (c : Code) (fuel code cert : Nat) :
    GorbowStandardInstances.instantiate (certificateMatrix pF c fuel code) (Term.numeral cert) =
      FiniteSource.checkerEquation pF c fuel code cert := by
  simp only [GorbowStandardInstances.instantiate, certificateMatrix, substituteFormula,
    substCall, substNum, List.Vector.map_cons, List.Vector.map_nil]
  rfl

private theorem existsIntroduction (T : Sentence → Prop) (a : Formula 1) (t : Term 0)
    (h : Derivation T (GorbowStandardInstances.instantiate a t)) :
    Nonempty (Derivation T (.ex a)) := by
  let P := Formula.all (.neg a)
  let A := GorbowStandardInstances.instantiate a t
  have hi : Derivation T (.imp P (.neg A)) := .logical (.allInstantiate (.neg a) t)
  have hp : Hilbert.Local T 0 [.neg (.neg P)] P :=
    .mp (.base (Hilbert.doubleNegation P)) (.hypothesis List.mem_cons_self)
  have hn : Hilbert.Local T 0 [] (.neg P) := Hilbert.Local.classical (.neg P)
    (Hilbert.Local.explosion (.neg P) (.base h) (.mp (.base hi) hp))
  exact ⟨.mp (.logical (.existsDualBackward a)) (Hilbert.Local.finish hn)⟩

theorem exactFiniteCodes : Targets.ExactFiniteCodes := by
  intro sentences I code
  induction sentences with
  | nil => simp [codeList, Formula.realize, Term.realize]
  | cons sigma rest ih =>
      simp only [codeList, Formula.realize, numeral_realize, Term.realize, Fin.cases_zero]
      rw [ih]
      constructor
      · rintro (h | ⟨tau, htau, he⟩)
        · exact ⟨sigma, List.mem_cons_self, h⟩
        · exact ⟨tau, List.mem_cons_of_mem _ htau, he⟩
      · rintro ⟨tau, htau, he⟩
        rcases List.mem_cons.mp htau with h | htau
        · subst tau
          exact Or.inl he
        · exact Or.inr ⟨tau, htau, he⟩

theorem actualInternalFiniteAxioms : Targets.ActualInternalFiniteAxioms := by
  intro pF pR q c hA
  obtain ⟨fuel, hstage, _, hcerts⟩ := FiniteSource.Proof.actualFixedFuelPackage pF pR q c hA
  let T := S pF pR q
  let phi := fixedFuelProvability pF c fuel
  have hclosed : ∀ sigma ∈ axiomsS pF pR q,
      Nonempty (Derivation T (closedAt phi (formulaCode sigma))) := by
    intro sigma hsigma
    obtain ⟨cert, _, ⟨dn⟩⟩ := hcerts sigma hsigma
    have dn' : Derivation T (GorbowStandardInstances.instantiate
        (certificateMatrix pF c fuel (formulaCode sigma)) (Term.numeral cert)) := by
      rw [instantiateCertificate]
      exact dn
    obtain ⟨de⟩ := existsIntroduction T _ (Term.numeral cert) dn'
    exact ⟨(closedFixedFuel pF c fuel (formulaCode sigma)).symm ▸ de⟩
  obtain ⟨dcases⟩ := finiteCases T phi (axiomsS pF pR q) hclosed
  exact ⟨fuel, hstage, ⟨.generalize dcases⟩⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource.Proof
