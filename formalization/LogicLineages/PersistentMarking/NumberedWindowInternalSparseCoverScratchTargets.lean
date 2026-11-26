module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverBoundsAlgorithm (cover)
open NumberedWindowScalarAlgorithm (Settings vertices)
open NumberedWindowInternalSparseCoverScratch

/-- The unchanged all-input calibration of the selected cover callback. -/
def ActualSelectedCoverOutput (C : Program 3) : Prop :=
  ∀ (H K : List Nat) (n : Nat),
    evaluate C (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil) =
      Encodable.encode (cover H K n)

/-- The original Option code preserves none versus some [], and the
scratch projection itself agrees exactly with the supplied Option value. -/
def ExactCoverOptionPayload : Prop :=
  ∀ p : Option (List Nat),
    evaluate optionPayload (Encodable.encode p ::ᵥ nil) = numbersNumber (p.getD [])

/-- One actual original selected C works for all fixed Settings, with
the original Option code still visible before the scratch-only projection. -/
def ExactSelectedCoverToScratch : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (s : Settings) (n : Nat),
      evaluate (coverOption C s) (n ::ᵥ nil) = Encodable.encode (cover s.window.2 s.types n) ∧
      evaluate (scratchVertices C s) (n ::ᵥ nil) = numbersNumber (vertices s n)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchTargets
