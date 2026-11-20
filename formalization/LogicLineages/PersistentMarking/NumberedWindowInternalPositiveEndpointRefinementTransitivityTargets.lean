module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)

/-- The same actual address/positive-fold program with only the
physical endpoint guards. Both supplied certificates and the common
middle term stay literal. A successful composed certificate for the
new wrapper is derived in the very same arbitrary body. -/
def ExactOpenEndpointRefinedAddressTransitivity : Prop :=
  ∀ (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
      (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (left first middle second right : OTerm α),
    let r := withEndpointCarriers i (addressPositive cv tv raw least)
    Nonempty (Derivation B Γ (accepts r left first middle)) →
    Nonempty (Derivation B Γ (accepts r middle second right)) →
    Nonempty (Derivation B Γ (suppliedEdge r left right))

/-- Actual original scalar edge transitivity with its original outer
context and certificate binders, at the rebuilt body for this very
same endpoint-refined program. The multiset/direct slice is unchanged. -/
def ExactInstalledEndpointRefinedScalarEdgeTransitivity : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
      (c : Nat) (α : Type) (left middle right : OTerm α),
    let r := withEndpointCarriers i (addressPositive cv tv raw least)
    let S := data i j r d
    let B := sourceBody S c
    Nonempty (Derivation B [] ((edge S false c left middle ⊓ edge S false c middle right).imp
      (edge S false c left right)))

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTransitivityTargets
