module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanNil)
open NumberedWindowInternalDirectInsertedScanTargets (scanLoop)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep zeroBase)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalOriginScanNilTargets

attribute [local irreducible] programGraph

theorem exact_OpenOriginScanNil : ExactOpenOriginScanNil := by
  intro side r B α Γ out scratchLeft rawSide filtered
  have base := nilRecover zeroBase (rowStep side) out ![scratchLeft] filtered
  have zero : Nonempty (Derivation B Γ (programGraph zeroBase z ![scratchLeft])) :=
    constantZeroValue ![scratchLeft]
  have same := valueUnique zeroBase z out ![scratchLeft] zero base
  exact headTransport (scanLoop r) oneTerm z out ![rawSide] same
    (exactOpenScanNil r B α Γ rawSide)

#print axioms exact_OpenOriginScanNil

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanNilProof
