module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalPairing LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Exact calibration to the pinned original Mathlib Nat.pair. -/
def ExactPairingEvaluation : Prop :=
  ∀ x y : Nat, evaluate pairing (x ::ᵥ y ::ᵥ List.Vector.nil) = Nat.pair x y

def ActualOriginalPairingGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y : OrdinaryArithmetic.Term α),
  let g := programGraph pairing out (Fin.cons x (Fin.cons y Fin.elim0))
  let s := pairingSpec out x y
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalPairingTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  Total body (OrdinaryArithmetic.graphFormula pairing) ∧
    Functional body (OrdinaryArithmetic.graphFormula pairing)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingTargets
