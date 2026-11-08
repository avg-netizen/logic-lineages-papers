module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalPathChecker NumberedQuotientPathCertificates
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every raw natural code is calibrated against the literal original path
test and decoder, with no successful-decoding premise. -/
def ActualOriginalPathCheckerEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (edge : Program 3),
  EdgeCalibrated n arity symbols S Gamma table edge →
  ∀ x y code : Nat,
    evaluate (checker edge false) (x ::ᵥ y ::ᵥ code ::ᵥ List.Vector.nil) =
      if pathTest n arity symbols S Gamma table x y ((decodePathCertificate code).getD []) then 1 else 0

def ActualOriginalPositivePathCheckerEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (edge : Program 3),
  EdgeCalibrated n arity symbols S Gamma table edge →
  ∀ x y code : Nat,
    evaluate (checker edge true) (x ::ᵥ y ::ᵥ code ::ᵥ List.Vector.nil) =
      if positivePathTest n arity symbols S Gamma table x y code then 1 else 0

def ActualInternalPathNil : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (α : Type)
    (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] ((pathGraph edge x y OrdinaryArithmetic.zeroTerm).iff (equal x y)))

def ActualInternalPositivePathNil : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (α : Type)
    (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (positiveGraph edge x y OrdinaryArithmetic.zeroTerm).not)

/-- Internal path acceptance unfolds on the original pair-coded entry and
cons graphs. The arbitrary edge Program needs no internal calibration premise. -/
def ActualInternalPathCons : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (α : Type)
    (x y code raw tail vertex certificate : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((consPremises code raw tail vertex certificate).imp
      ((pathGraph edge x y code).iff
        (edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail))))

def ActualInternalPositivePathCons : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 3) (α : Type)
    (x y code raw tail vertex certificate : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((consPremises code raw tail vertex certificate).imp
      ((positiveGraph edge x y code).iff
        (edgeGraph edge x vertex certificate ⊓ pathGraph edge vertex y tail))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerTargets
