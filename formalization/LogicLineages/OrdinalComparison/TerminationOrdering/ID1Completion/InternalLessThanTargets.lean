module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalLessThan
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Natural-number calibration is not an object-language reflection rule. -/
def ExactLessThanEvaluation : Prop :=
  ∀ x y : Nat, evaluate ltTest (x ::ᵥ y ::ᵥ List.Vector.nil) = if x < y then 1 else 0

def ActualOriginalLessThanAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  let g := programGraph ltTest (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
    (Fin.cons x (Fin.cons y Fin.elim0))
  let s := strictLess x y
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalLessThanRejection : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (x y : OrdinaryArithmetic.Term α),
  let g := programGraph ltTest OrdinaryArithmetic.zeroTerm (Fin.cons x (Fin.cons y Fin.elim0))
  let s := (strictLess x y).not
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

/-- Exact 0/1 graph for arbitrary original object-language terms, not merely numerals. -/
def ActualOriginalLessThanGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y : OrdinaryArithmetic.Term α),
  let g := programGraph ltTest out (Fin.cons x (Fin.cons y Fin.elim0))
  let s := lessThanSpec out x y
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanTargets
