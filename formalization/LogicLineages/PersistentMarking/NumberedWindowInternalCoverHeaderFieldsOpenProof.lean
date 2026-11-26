module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelope (nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverHeaderFieldsTargets
open NumberedWindowInternalCoverHeaderFieldsSelectorsProof (selectorCases)

theorem exact_OpenCoverHeaderFields : ExactOpenCoverHeaderFields := by
  intro tag arity body α Γ q goal good next
  apply selectorCases body arity α Γ q cellTail goal
  intro β j Δ fields keep len reports
  have g := moveReport j Δ keep (header tag arity) (suc z) q good
  simp only [header,sucRelabel,zRelabel] at g
  have slotTag : Nonempty (Derivation body Δ (unary (literal 1 tag) (numeral tag) (q.relabel j))) :=
    literalGraph tag ![q.relabel j]
  have ar : Nonempty (Derivation body Δ
      (unary (nodeGood (literal 1 tag) fields.length) (suc z) (q.relabel j))) := by
    rw [len]
    exact g
  have same := readNode (literal 1 tag) (q.relabel j) (numeral tag) fields slotTag ar reports
  exact next β j Δ fields keep len reports same

#print axioms exact_OpenCoverHeaderFields

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
