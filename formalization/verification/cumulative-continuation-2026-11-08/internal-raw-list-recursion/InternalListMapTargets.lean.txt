module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact original encoder/decoder calibration on every natural input. -/
def ActualRawListMapEvaluation : Prop :=
  ∀ (k : Nat) (transform : Program (k + 1)) (params : List.Vector Nat k) (code : Nat),
  evaluate (InternalListMap.map transform) (code ::ᵥ params) =
    numbersNumber (((decodeNumbers code).getD []).map
      (fun head => evaluate transform (head ::ᵥ params)))

def ActualOriginalListMapZero : Prop :=
  ∀ (body : Positive (Fin 1)) (k : Nat) (transform : Program (k + 1)) (α : Type)
    (out : OrdinaryArithmetic.Term α) (params : Fin k → OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph (InternalListMap.map transform) out (Fin.cons OrdinaryArithmetic.zeroTerm params)).iff
      (equal out OrdinaryArithmetic.zeroTerm)))

/-- The concrete map AST preserves the literal constructor. The supplied
head/tail computations are actual original graph derivations, not semantic
evaluations or assumptions of successful decoding. -/
def ActualOriginalListMapCons : Prop :=
  ∀ (body : Positive (Fin 1)) (k : Nat) (transform : Program (k + 1)) (α : Type)
    (code head tail mappedHead mappedTail out : OrdinaryArithmetic.Term α)
    (params : Fin k → OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))) ⊓
      ((programGraph transform mappedHead (Fin.cons head params)) ⊓
        (programGraph (InternalListMap.map transform) mappedTail (Fin.cons tail params)))).imp
      ((programGraph (InternalListMap.map transform) out (Fin.cons code params)).iff
        (programGraph consCode out (Fin.cons mappedHead (Fin.cons mappedTail Fin.elim0))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapTargets
