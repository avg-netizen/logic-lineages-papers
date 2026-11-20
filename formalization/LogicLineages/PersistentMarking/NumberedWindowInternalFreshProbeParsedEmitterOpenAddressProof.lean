module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterOpenAddressProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeParsedEmitter
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary Reports)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (cellEquation)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)

/-- Both literal sparse equations use the same actual reported raw
result. No object reasoning consumes a numerical decoder claim. -/
theorem exactOpenCoordinates : ExactOpenAddressArrowCoordinates := by
  intro body α Γ q c r d e k hn ha ⟨haddr⟩ ⟨harrow⟩
  have hc := Derivation.conjunctionLeft haddr
  have hr := Derivation.conjunctionLeft (Derivation.conjunctionRight haddr)
  have hk := Derivation.conjunctionRight (Derivation.conjunctionRight haddr)
  have hd := Derivation.conjunctionLeft harrow
  have he := Derivation.conjunctionRight harrow
  have tag : Nonempty (Derivation body Γ (programGraph addressTag (numeral 3) ![q])) := by
    unfold addressTag
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 3 ![q]
  have reps : Reports body Γ q cellTail [c,r,k] :=
    ⟨⟨hc⟩,⟨hr⟩,⟨hk⟩,True.intro⟩
  obtain ⟨dq⟩ := readNode addressTag q (numeral 3) [c,r,k] tag hn reps
  obtain ⟨dr⟩ := cellEquation r d e
    (takeUnary cellGood rawResult (suc z) q r ha ⟨hr⟩)
    (takeUnary cellHead rawResult d q r ⟨hd⟩ ⟨hr⟩)
    (takeUnary cellTail rawResult e q r ⟨he⟩ ⟨hr⟩)
  simp only [sourceShape,equalEqn]
  exact ⟨Derivation.conjunctionIntroduction dq dr⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterOpenAddressProof
