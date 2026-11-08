module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedPathChecker NumberedQuotientPathCertificates
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All raw natural codes retain the literal original decoder and reflexive
path test at the same calibrated parameter; no decoding-success premise. -/
def ActualOriginalParameterizedPathCheckerEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (edge : Program 4) (parameter : Nat),
  EdgeCalibrated n arity symbols S Gamma table edge parameter →
  ∀ x y code : Nat,
    evaluate (checker edge false) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if pathTest n arity symbols S Gamma table x y ((decodePathCertificate code).getD []) then 1 else 0

/-- Original positive acceptance on every raw code, with its literal nil
rejection and the unchanged runtime parameter in every edge evaluation. -/
def ActualOriginalParameterizedPositivePathCheckerEvaluation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (edge : Program 4) (parameter : Nat),
  EdgeCalibrated n arity symbols S Gamma table edge parameter →
  ∀ x y code : Nat,
    evaluate (checker edge true) (x ::ᵥ y ::ᵥ code ::ᵥ parameter ::ᵥ List.Vector.nil) =
      if positivePathTest n arity symbols S Gamma table x y code then 1 else 0

def ActualInternalParameterizedPathNil : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (α : Type)
    (x y parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((pathGraph edge x y OrdinaryArithmetic.zeroTerm parameter).iff (equal x y)))

def ActualInternalParameterizedPositivePathNil : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (α : Type)
    (x y parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body [] (positiveGraph edge x y OrdinaryArithmetic.zeroTerm parameter).not)

/-- The original paired entry and cons expose one edge and the reflexive
tail at an arbitrary symbolic parameter. No semantic premise is used. -/
def ActualInternalParameterizedPathCons : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (α : Type)
    (x y code raw tail vertex certificate parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((consPremises code raw tail vertex certificate).imp
      ((pathGraph edge x y code parameter).iff
        (edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter))))

def ActualInternalParameterizedPositivePathCons : Prop :=
  ∀ (body : Positive (Fin 1)) (edge : Program 4) (α : Type)
    (x y code raw tail vertex certificate parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((consPremises code raw tail vertex certificate).imp
      ((positiveGraph edge x y code parameter).iff
        (edgeGraph edge x vertex certificate parameter ⊓ pathGraph edge vertex y tail parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerTargets
