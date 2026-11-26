module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalMatchReductionTargets (suppliedEdge)
open NumberedWindowInternalSparseAddressPositive (addressPositive)

/-- Same r and original fixed lexical fiber in the object calculus.
Both input certificates are supplied and remain on their own tapes.
The conclusion binds a genuine raw certificate for the same r. -/
def ExactInstalledAddressTransitivity : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
    (c : Nat) (α : Type) (left first middle second right : OTerm α),
    let r := addressPositive cv tv raw least
    let B := sourceBody (data i j r d) c
    Nonempty (Derivation B [] ((accepts r left first middle ⊓ accepts r middle second right).imp
      (suppliedEdge r left right)))

/-- Transitivity of the actual original scalar edge formula, including
both original certificate binders and outer context. No I/J claim. -/
def ExactInstalledScalarEdgeTransitivity : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
    (c : Nat) (α : Type) (left middle right : OTerm α),
    let r := addressPositive cv tv raw least
    let S := data i j r d
    let B := sourceBody S c
    Nonempty (Derivation B [] ((edge S false c left middle ⊓ edge S false c middle right).imp
      (edge S false c left right)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressTransitivityTargets
