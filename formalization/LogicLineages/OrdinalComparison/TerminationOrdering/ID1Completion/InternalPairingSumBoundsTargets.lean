module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalPairingSumBounds

/-- Both coordinates together are bounded by the ORIGINAL pair output. -/
def ActualOriginalPairingSumBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (p x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((pairGraph p x y).imp (weakBound (OrdinaryArithmetic.addTerm x y) p)))

/-- The two actual child validator counts fit inside the original parent PAYLOAD.
This is fp+ap+2 ≤ payload, with no bound on the reconstructed typed child codes. -/
def ActualOriginalApplicationPayloadChildFuelBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type)
    (payload middle children d fp ap : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((applicationPayloadWitnesses payload middle children d fp ap).imp
      (weakBound (childFuelSum fp ap) payload)))

/-- One parent-opening step plus both child counts fit into the exact original
parent validator count payload+1. The extra step is an arithmetic successor,
not an external iteration count or a stronger fuel supplied as a premise. -/
def ActualOriginalApplicationParentFuelBound : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type)
    (payload middle children d fp ap : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((applicationPayloadWitnesses payload middle children d fp ap).imp
      (weakBound (OrdinaryArithmetic.succTerm (childFuelSum fp ap))
        (OrdinaryArithmetic.succTerm payload))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsTargets
