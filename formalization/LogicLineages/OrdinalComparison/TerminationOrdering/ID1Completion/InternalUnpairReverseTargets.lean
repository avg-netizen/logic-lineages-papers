module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph

/-- Reverse inverse on every arbitrary object-language input and coordinate witnesses. -/
def ActualOriginalUnpairReverseInverse : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph InternalUnpair.left x (Fin.cons n Fin.elim0)) ⊓
      (programGraph InternalUnpair.right y (Fin.cons n Fin.elim0))).imp
      (programGraph InternalPairing.pairing n (Fin.cons x (Fin.cons y Fin.elim0)))))

/-- Both coordinate bounds for the unchanged original pair graph. -/
def ActualOriginalPairingCoordinateBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph InternalPairing.pairing n (Fin.cons x (Fin.cons y Fin.elim0))).imp
      (InternalUnpairReverse.coordinateBounds n x y)))

/-- Both unpair coordinate bounds on every arbitrary original input. -/
def ActualOriginalUnpairCoordinateBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (n x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph InternalUnpair.left x (Fin.cons n Fin.elim0)) ⊓
      (programGraph InternalUnpair.right y (Fin.cons n Fin.elim0))).imp
      (InternalUnpairReverse.coordinateBounds n x y)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseTargets
