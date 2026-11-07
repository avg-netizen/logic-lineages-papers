module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Standard evaluation calibration is not an object-language inference rule. -/
def ExactPredecessorEvaluation : Prop :=
  ∀ x : Nat, evaluate predecessor (x ::ᵥ List.Vector.nil) = x.pred

def ExactSubtractionEvaluation : Prop :=
  ∀ x y : Nat, evaluate subtract (x ::ᵥ y ::ᵥ List.Vector.nil) = y - x

def ExactEqualityEvaluation : Prop :=
  ∀ x y : Nat, evaluate equalityTest (x ::ᵥ y ::ᵥ List.Vector.nil) = if x = y then 1 else 0

def ActualOriginalPredecessorGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out input : OrdinaryArithmetic.Term α),
  let g := programGraph predecessor out (Fin.cons input Fin.elim0)
  let s := predecessorSpec out input
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

/-- Subtracting x from x+y returns y for arbitrary object-language terms. -/
def ActualOriginalSubtractionDiagonal : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (programGraph subtract y
    (Fin.cons x (Fin.cons (OrdinaryArithmetic.addTerm x y) Fin.elim0))))

/-- Subtracting x+y from x returns zero. -/
def ActualOriginalSubtractionAbsorption : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (programGraph subtract OrdinaryArithmetic.zeroTerm
    (Fin.cons (OrdinaryArithmetic.addTerm x y) (Fin.cons x Fin.elim0))))

/-- Acceptance means exactly output ONE, not arbitrary nonzero output.
The conclusion is an actual original InternalCalculus derivation, with no
supplied correctness premise and no semantic reflection rule. -/
def ActualOriginalEqualityAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  let g := programGraph equalityTest (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    (Fin.cons x (Fin.cons y Fin.elim0))
  let s := equal x y
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestTargets
