module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge

/-- Both directions for every original arithmetic input/output term and every
original positive inductive body, without a supplied correctness assumption. -/
def ActualOriginalZeroTestGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out input : OTerm α),
  let g := programGraph GorbowPRInternalControl.zeroTest out (Fin.cons input Fin.elim0)
  let s := testSpec out input OrdinaryArithmetic.zeroTerm
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalConditionalGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out control zeroBranch otherBranch : OTerm α),
  let g := programGraph GorbowPRInternalControl.conditional out
    (Fin.cons control (Fin.cons zeroBranch (Fin.cons otherBranch Fin.elim0)))
  let s := conditionalSpec out control zeroBranch otherBranch
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

/-- Equality to ONE, not generic nonzero acceptance. -/
def ActualOriginalEqualsOneGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out input : OTerm α),
  let g := programGraph GorbowVerifierNormalization.equalsOne out (Fin.cons input Fin.elim0)
  let s := testSpec out input (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphTargets
