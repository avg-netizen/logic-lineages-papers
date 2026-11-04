module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticLeastSchemasProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaProof
@[expose] public section

/-! A finitary first-order proof judgment for ONE positive arithmetic inductive
definition. Logical rules manipulate syntax; no constructor accepts semantic
truth, accessibility, computability, or a source reduction theorem. The body
has only its object variable free. Parameters in invariants are ordinary free
first-order variables, not parameters of a second inductive definition. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticSchemas
open PositiveArithmeticPredicateSubstitution PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof

abbrev Formula (α : Type) := language.Formula α
abbrev Term (α : Type) := language.Term α

def instantiate {α : Type} (theta : Formula (α ⊕ Fin 1)) (t : Term α) : Formula α :=
  theta.subst (Sum.elim Term.var (fun _ => t))

def weaken {α : Type} (phi : Formula α) : Formula (α ⊕ Fin 1) := phi.relabel Sum.inl

def bodyWithParameters (body : Positive (Fin 1)) (α : Type) : Positive (α ⊕ Fin 1) :=
  PositiveArithmeticTransforms.relabel Sum.inr body

def replacedBody (body : Positive (Fin 1)) {α : Type}
    (theta : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  substitutePredicate (bodyWithParameters body α) (liftPredicateFormula theta)

def successorInstance {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  theta.subst (Sum.elim (fun a => Term.var (.inl a))
    (fun _ => arithmeticEmbedding.onTerm (OrdinaryArithmetic.succTerm (.var (.inr 0)))))

def naturalInductionSchema {α : Type} (theta : Formula (α ⊕ Fin 1)) : Formula α :=
  ((instantiate theta (arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm)) ⊓
    allOne (theta.imp (successorInstance theta))).imp (allOne theta)

inductive ArithmeticInstance (α : Type) where
  | successorNotZero (t : OrdinaryArithmetic.Term α)
  | successorInjective (t u : OrdinaryArithmetic.Term α)
  | additionZero (t : OrdinaryArithmetic.Term α)
  | additionSuccessor (t u : OrdinaryArithmetic.Term α)
  | multiplicationZero (t : OrdinaryArithmetic.Term α)
  | multiplicationSuccessor (t u : OrdinaryArithmetic.Term α)
  | induction (theta : Formula (α ⊕ Fin 1))

def arithmeticFormula {α : Type} : ArithmeticInstance α → Formula α
  | .successorNotZero t =>
      (arithmeticEmbedding.onFormula ((OrdinaryArithmetic.succTerm t).equal OrdinaryArithmetic.zeroTerm)).not
  | .successorInjective t u => arithmeticEmbedding.onFormula
      (((OrdinaryArithmetic.succTerm t).equal (OrdinaryArithmetic.succTerm u)).imp (t.equal u))
  | .additionZero t => arithmeticEmbedding.onFormula ((OrdinaryArithmetic.addTerm t OrdinaryArithmetic.zeroTerm).equal t)
  | .additionSuccessor t u => arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.addTerm t (OrdinaryArithmetic.succTerm u)).equal
        (OrdinaryArithmetic.succTerm (OrdinaryArithmetic.addTerm t u)))
  | .multiplicationZero t => arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.mulTerm t OrdinaryArithmetic.zeroTerm).equal OrdinaryArithmetic.zeroTerm)
  | .multiplicationSuccessor t u => arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.mulTerm t (OrdinaryArithmetic.succTerm u)).equal
        (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm t u) t))
  | .induction theta => naturalInductionSchema theta

/-- Used only to check soundness of the explicit rules. This is not a
derivation rule or a premise of any internal induction theorem. -/
def InductiveModel (body : Positive (Fin 1)) (P : Nat → Prop) : Prop :=
  (∀ (α : Type) (v : α → Nat),
    realize P (closureSchema (bodyWithParameters body α)) v) ∧
  (∀ (α : Type) (theta : Formula (α ⊕ Fin 1)) (v : α → Nat),
    realize P (leastnessSchema (bodyWithParameters body α) theta) v)

def standardLeastPredicate (body : Positive (Fin 1)) (x : Nat) : Prop :=
  x ∈ PositiveArithmeticLeastSet.leastSet
    (PositiveArithmeticTransforms.relabel (fun _ => (1 : Fin 2)) body) 0

/-- A finite natural-deduction tree. ID1 supplies exactly closure and the
leastness schema for the one fixed positive body; PA induction admits the
entire expanded first-order language. -/
inductive Derivation (body : Positive (Fin 1)) : {α : Type} → List (Formula α) → Formula α → Type 1
  | hypothesis {α} {Gamma : List (Formula α)} {phi} : phi ∈ Gamma → Derivation body Gamma phi
  | weakening {α} {Gamma Delta : List (Formula α)} {phi} :
      (∀ p, p ∈ Gamma → p ∈ Delta) → Derivation body Gamma phi → Derivation body Delta phi
  | implicationIntroduction {α} {Gamma : List (Formula α)} {phi psi} :
      Derivation body (phi :: Gamma) psi → Derivation body Gamma (phi.imp psi)
  | implicationElimination {α} {Gamma : List (Formula α)} {phi psi} :
      Derivation body Gamma (phi.imp psi) → Derivation body Gamma phi → Derivation body Gamma psi
  | conjunctionIntroduction {α} {Gamma : List (Formula α)} {phi psi} :
      Derivation body Gamma phi → Derivation body Gamma psi → Derivation body Gamma (phi ⊓ psi)
  | conjunctionLeft {α} {Gamma : List (Formula α)} {phi psi} :
      Derivation body Gamma (phi ⊓ psi) → Derivation body Gamma phi
  | conjunctionRight {α} {Gamma : List (Formula α)} {phi psi} :
      Derivation body Gamma (phi ⊓ psi) → Derivation body Gamma psi
  | explosion {α} {Gamma : List (Formula α)} {phi} :
      Derivation body Gamma ⊥ → Derivation body Gamma phi
  | classical {α} {Gamma : List (Formula α)} {phi} :
      Derivation body (phi.not :: Gamma) ⊥ → Derivation body Gamma phi
  | universalIntroduction {α} {Gamma : List (Formula α)} {phi : Formula (α ⊕ Fin 1)} :
      Derivation body (Gamma.map weaken) phi → Derivation body Gamma (allOne phi)
  | universalElimination {α} {Gamma : List (Formula α)} {phi : Formula (α ⊕ Fin 1)} (t : Term α) :
      Derivation body Gamma (allOne phi) → Derivation body Gamma (instantiate phi t)
  | existentialIntroduction {α} {Gamma : List (Formula α)} {phi : Formula (α ⊕ Fin 1)} (t : Term α) :
      Derivation body Gamma (instantiate phi t) → Derivation body Gamma (existsOne phi)
  | existentialElimination {α} {Gamma : List (Formula α)} {phi : Formula (α ⊕ Fin 1)} {psi} :
      Derivation body Gamma (existsOne phi) →
      Derivation body (phi :: Gamma.map weaken) (weaken psi) → Derivation body Gamma psi
  | equalityReflexivity {α} {Gamma : List (Formula α)} (t : Term α) :
      Derivation body Gamma (t.equal t)
  | equalityElimination {α} {Gamma : List (Formula α)} (theta : Formula (α ⊕ Fin 1)) (t u : Term α) :
      Derivation body Gamma (t.equal u) → Derivation body Gamma (instantiate theta t) →
      Derivation body Gamma (instantiate theta u)
  | arithmetic {α} {Gamma : List (Formula α)} (w : ArithmeticInstance α) :
      Derivation body Gamma (arithmeticFormula w)
  | inductiveClosure {α} {Gamma : List (Formula α)} :
      Derivation body Gamma (closureSchema (bodyWithParameters body α))
  | inductiveLeastness {α} {Gamma : List (Formula α)} (theta : Formula (α ⊕ Fin 1)) :
      Derivation body Gamma (leastnessSchema (bodyWithParameters body α) theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus
