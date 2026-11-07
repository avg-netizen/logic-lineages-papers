module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph

/-- The original pair graph entails both literal unpair coordinate graphs.
All free-variable types, terms and positive operator bodies remain arbitrary. -/
def ActualOriginalGeneratedCodeInverse : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (p x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph InternalPairing.pairing p (Fin.cons x (Fin.cons y Fin.elim0))).imp
      ((programGraph InternalUnpair.left x (Fin.cons p Fin.elim0)) ⊓
       (programGraph InternalUnpair.right y (Fin.cons p Fin.elim0)))))

/-- Totality and functionality concern original graphFormula, not evaluation. -/
def ActualOriginalUnpairTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  (InternalGraphComposition.Total body (OrdinaryArithmetic.graphFormula InternalUnpair.left) ∧
   InternalGraphComposition.Functional body (OrdinaryArithmetic.graphFormula InternalUnpair.left)) ∧
  (InternalGraphComposition.Total body (OrdinaryArithmetic.graphFormula InternalUnpair.right) ∧
   InternalGraphComposition.Functional body (OrdinaryArithmetic.graphFormula InternalUnpair.right))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairTargets
