module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

def ExactOpenConstructorHeadFiniteCases : Prop :=
  ∀ (heads : List Nat) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (head : OTerm α) (goal : Formula α),
    D B Γ (memberGraph (numeral (numbersNumber heads)) head) →
    (∀ n ∈ heads, D B (eqn head (numeral n) :: Γ) goal) →
    D B Γ goal

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteTargets
