module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpoint
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open TaggedArithmeticOperators SourceComputabilityFormulaSupportProof InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Ordinary term substitution, including the context code specialization.
It changes neither the source arithmetic graphs nor the positive grammar. -/
def substitutePositive : {α β : Type} → (α → OrdinaryArithmetic.Term β) → Positive α → Positive β
  | _, _, ts, .arithmetic phi => .arithmetic (phi.subst ts)
  | _, _, ts, .predicate t => .predicate (t.subst ts)
  | _, _, ts, .conj p q => .conj (substitutePositive ts p) (substitutePositive ts q)
  | _, _, ts, .guarded guard p => .guarded (guard.subst ts) (substitutePositive ts p)
  | _, _, ts, .all p => .all (substitutePositive
      (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i))) p)

/-- These choices select the ALREADY PROVED original graph suppliers, rather
than an arbitrary extensionally equivalent positive operator. No effectivity
of Classical.choose is asserted. Their programs and formulas remain fixed
while the source window/context varies. -/
noncomputable def scalarCarrier (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    OrdinaryArithmetic.Formula (Fin 2) :=
  Classical.choose (OrdinaryArithmeticCarrierProof.encodedCarrierFormulas n arity Gamma)

noncomputable def multisetCarrier (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    OrdinaryArithmetic.Formula (Fin 2) :=
  Classical.choose (Classical.choose_spec (OrdinaryArithmeticCarrierProof.encodedCarrierFormulas n arity Gamma))

noncomputable def positiveProgram (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : Program 4 :=
  Classical.choose (Classical.choose_spec (OrdinaryArithmeticQuotientProof.encodedHAndPositiveR n arity Gamma))

noncomputable def multisetProgram (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : Program 4 :=
  Classical.choose (OrdinaryArithmeticDirectProof.encodedDirectFormula n arity Gamma)

noncomputable def scalarOperator (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : Positive (Fin 2) :=
  accessibilityOperator (scalarCarrier n arity Gamma)
    (OrdinaryArithmeticQuotient.certificateGraph (positiveProgram n arity Gamma))

noncomputable def multisetOperator (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) : Positive (Fin 2) :=
  accessibilityOperator (multisetCarrier n arity Gamma)
    (OrdinaryArithmeticQuotient.certificateGraph (multisetProgram n arity Gamma))

/-- Single ID1 operator: even codes are I, odd codes are J. The original
context code is a closed numeral, so no operator parameter remains free. -/
noncomputable def sourceBody (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) : Positive (Fin 1) :=
  substitutePositive ![numeral context,.var 0]
    (combinedOperator (scalarOperator n arity Gamma) (multisetOperator n arity Gamma))

def strictTotalPrecedence {n : Nat} (table : Fin n → Fin n → Bool) : Prop :=
  (∀ f, table f f = false) ∧
  (∀ f g h, table f g = true → table g h = true → table f h = true) ∧
  (∀ f g, f ≠ g → table f g = true ∨ table g f = true)

/-- The printed all-term endpoint, as one CLOSED first-order theorem in the
single-operator calculus. The antecedent is the exact original typed scalar
carrier. Membership is in its even slice, with no assumption of termination. -/
noncomputable def allTermsFormula (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) : Formula Empty :=
  allOne ((arithmeticEmbedding.onFormula ((scalarCarrier n arity Gamma).subst
      ![numeral context,.var (.inr 0)])).imp
    (Positive.predicate (tagTerm false (.var (.inr (0 : Fin 1))))).formula)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceEndpoint
