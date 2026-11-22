module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXProof (exact_OpenCoverCombinedRestrictedDirectedX)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalCoverCombinedRestrictedCommonCoverProof (exact_OpenCoverCombinedRestrictedCommonCover)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof (guardedOfActualPair)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets

theorem exact_OpenCoverCombinedRestrictedPairedAux : ExactOpenCoverCombinedRestrictedPairedAux := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal P W D X a b syn guards argument fg gf ma mb k
  obtain ⟨forward⟩ := exact_OpenCoverCombinedRestrictedDirectedX V TV M M0 B T base s body α Γ
    ctx dom cod f g arg syn guards argument fg
  obtain ⟨reverse⟩ := exact_OpenCoverCombinedRestrictedDirectedX V TV M M0 B T base s body α Γ
    ctx dom cod g f arg syn guards argument gf
  obtain ⟨abLaw⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx cod a b
  obtain ⟨baLaw⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx cod b a
  have ab := Derivation.implicationElimination (Derivation.conjunctionLeft abLaw) forward
  have ba := Derivation.implicationElimination (Derivation.conjunctionLeft baLaw) reverse
  have ws := Derivation.conjunctionRight ab
  have left : Nonempty (Derivation body Γ (windowAt W ctx cod a)) := ⟨Derivation.conjunctionLeft ws⟩
  have right : Nonempty (Derivation body Γ (windowAt W ctx cod b)) := ⟨Derivation.conjunctionRight ws⟩
  have forwardX : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape a b))) :=
    ⟨Derivation.conjunctionLeft ab⟩
  have reverseX : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape b a))) :=
    ⟨Derivation.conjunctionLeft ba⟩
  have va := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx cod a left
  have vb := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx cod b right
  apply exact_OpenCoverCombinedRestrictedCommonCover V TV M M0 B T s body α Γ a b m goal va.valid vb.valid ma mb
  intro β j Δ vertices keep ca cb
  have forward' := renameInto forwardX j Δ keep
  have reverse' := renameInto reverseX j Δ keep
  simp only [exchangeTape,programRename,binaryInputsRename,sucRelabel,zRelabel] at forward' reverse'
  have physical := guardedOfActualPair P.cover s D (a.relabel j) (b.relabel j) (suc vertices)
    forward' reverse' ca cb
  have left' := renameInto left j Δ keep
  have right' := renameInto right j Δ keep
  rw [windowRename] at left' right'
  obtain ⟨left'⟩ := left'
  obtain ⟨right'⟩ := right'
  obtain ⟨physical⟩ := physical
  obtain ⟨parentLaw⟩ := exact_OpenPackedScalarEdge X W body β Δ (ctx.relabel j) (cod.relabel j)
    (a.relabel j) (b.relabel j)
  have edge := Derivation.implicationElimination (Derivation.conjunctionRight parentLaw)
    (Derivation.conjunctionIntroduction physical (Derivation.conjunctionIntroduction left' right'))
  exact k β j Δ vertices keep ca cb ⟨edge⟩

#print axioms exact_OpenCoverCombinedRestrictedPairedAux
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof
