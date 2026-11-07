module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalOriginalOrderSyntaxProof InternalBetaModulusCoprimality
/-- Explicit predecessor of the positive enlarged common multiple. -/
def scalePred {α : Type} (b k : OrdinaryArithmetic.Term α) : OrdinaryArithmetic.Term α :=
  add (mul b (suc k)) k
/-- Enlarging a positive difference common multiple preserves every required divisor. -/
def ActualScaleMultiples : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (b k n : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (differenceMultiples (suc b) n)) →
  Nonempty (Derivation body Gamma (differenceMultiples (suc (scalePred b k)) n))
/-- Every residue below k is below every literal beta modulus of the enlarged scale. -/
def ActualResidueBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (b k i r : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma (ltF r k)) →
  Nonempty (Derivation body Gamma (ltF r (InternalBetaWitness.modulus (suc (scalePred b k)) i)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalResidueBoundTargets
