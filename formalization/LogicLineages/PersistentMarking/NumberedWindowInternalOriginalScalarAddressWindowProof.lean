module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The real original scalar acceptance at the held audited address
reports the actual original typed window and least at precisely its
physical raw representative. -/
theorem exact_OpenOriginalScalarAddressWindow (cv tv : Program 1) (W L : Program 3)
    (addr c ty raw : OTerm α)
    (fields : Nonempty (Derivation B Γ (addressReport addr c ty raw)))
    (i : Nonempty (Derivation B Γ (unary (addressScalar cv tv W L) (suc z) addr))) :
    Nonempty (Derivation B Γ
      (windowAt W c ty raw ⊓ programGraph L (suc raw) ![c,ty,raw])) := by
  obtain ⟨read⟩ := reported cv tv W L B α Γ addr c ty raw
  obtain ⟨coordinate⟩ := openTest W L B α Γ c ty raw
  obtain ⟨fields⟩ := fields
  obtain ⟨i⟩ := i
  have laws := Derivation.implicationElimination read fields
  have graph := Derivation.implicationElimination (Derivation.conjunctionLeft laws) i
  have valid := Derivation.conjunctionRight (Derivation.conjunctionRight graph)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft coordinate) valid⟩

#print axioms exact_OpenOriginalScalarAddressWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalScalarAddressWindowProof
