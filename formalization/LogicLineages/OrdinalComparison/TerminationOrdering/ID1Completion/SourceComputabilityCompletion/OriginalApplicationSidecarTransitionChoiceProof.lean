module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionChoiceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalApplicationSidecarTransitionPipelineDefinitions OriginalApplicationSidecarTransitionPipelineProof
open OriginalApplicationSidecarTransitionGraphProof


open InternalParameterizedBoundedDescentNormalizer
open InternalOriginalOrderSyntaxProof (ltF)
open InternalPositiveUnfoldingSupportProof (weakenClosed)
open InternalBetaTotalityProof (disjunctionElimination)

/-- Construct the literal candidate-valid/type/strict guard from actual facts. -/
theorem guardValue (valid : Program 2)
    (candidate input typ parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (validGraph valid candidate parameter)))
    (hlc : Nonempty (Derivation body Delta (leftGraph typ candidate)))
    (hli : Nonempty (Derivation body Delta (leftGraph typ input)))
    (hless : Nonempty (Derivation body Delta (ltF candidate input))) :
    Nonempty (Derivation body Delta (graph3 (guard valid) (suc z) candidate input parameter)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term alpha :=
    Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))
  have hl : Nonempty (Derivation body Delta (programGraph candidateLess (suc z) xs)) :=
    InternalApplicationCertificateConstructorsSupportProof.binaryValue InternalLessThan.ltTest
      (.projection 0) (.projection 1) (suc z) candidate input xs
      (InternalLessThanSupportProof.acceptOfLess candidate input hless)
      (projectionValue 0 xs) (projectionValue 1 xs)
  have hv : Nonempty (Derivation body Delta (programGraph (candidateValid valid) (suc z) xs)) :=
    InternalApplicationCertificateConstructorsSupportProof.binaryValue valid
      (.projection 0) (.projection 2) (suc z) candidate parameter xs hc
      (projectionValue 0 xs) (projectionValue 2 xs)
  have hcl := InternalApplicationCertificateConstructorsSupportProof.unaryValue InternalUnpair.left
    (.projection 0) typ candidate xs hlc (projectionValue 0 xs)
  have hil := InternalApplicationCertificateConstructorsSupportProof.unaryValue InternalUnpair.left
    (.projection 1) typ input xs hli (projectionValue 1 xs)
  have hs : Nonempty (Derivation body Delta (programGraph sameLeft (suc z) xs)) :=
    InternalApplicationStepPeelSupportProof.sameAccept _ _ typ xs hcl hil
  exact InternalAcceptanceConjunctionProof.conjunctionAccept _ _ xs hl
    (InternalAcceptanceConjunctionProof.conjunctionAccept _ _ xs hv hs)

/-- Equality suffices even when the strict-descent guard rejects. -/
theorem chooseEqual (valid : Program 2)
    (candidate input parameter : OrdinaryArithmetic.Term alpha)
    (he : Nonempty (Derivation body Delta (eqn candidate input))) :
    Nonempty (Derivation body Delta (graph3 (choose valid) candidate candidate input parameter)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term alpha :=
    Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))
  let accepted := graph3 (guard valid) (suc z) candidate input parameter
  apply formulaCases accepted
  · exact InternalAcceptanceBranchProof.successorBranchIntro (guard valid) (.projection 1) (.projection 0)
      candidate z xs ⟨Derivation.hypothesis List.mem_cons_self⟩ (projectionValue 0 xs)
  · have hz : Nonempty (Derivation body (accepted.not :: Delta) (programGraph (guard valid) z xs)) :=
      InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject _ _ xs
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he'⟩ := withHyp he accepted.not
    have hp : Nonempty (Derivation body (accepted.not :: Delta)
        (programGraph (.projection (1 : Fin 3)) candidate xs)) :=
      outputTransport (.projection 1) input candidate xs ⟨symm he'⟩ (projectionValue 1 xs)
    exact InternalAcceptanceBranchProof.zeroBranchIntro (guard valid) (.projection 1) (.projection 0)
      candidate xs hz hp

/-- The original weak order splits internally into strict descent or equality. -/
theorem chooseBounded (valid : Program 2)
    (candidate input typ parameter : OrdinaryArithmetic.Term alpha)
    (hc : Nonempty (Derivation body Delta (validGraph valid candidate parameter)))
    (hlc : Nonempty (Derivation body Delta (leftGraph typ candidate)))
    (hli : Nonempty (Derivation body Delta (leftGraph typ input)))
    (hb : Nonempty (Derivation body Delta (atMost candidate input))) :
    Nonempty (Derivation body Delta (graph3 (choose valid) candidate candidate input parameter)) := by
  obtain ⟨split⟩ := InternalLeastNumberProof.actualRightSuccessorSplit body alpha candidate input
  rw [InternalSourceInversionSupportProof.onEquality] at split
  obtain ⟨hb⟩ := hb
  have hd : Derivation body Delta (ltF candidate input ⊔ eqn candidate input) :=
    Derivation.implicationElimination (weakenClosed split Delta) hb
  have strict : Nonempty (Derivation body (ltF candidate input :: Delta)
      (graph3 (choose valid) candidate candidate input parameter)) := by
    have hg := guardValue valid candidate input typ parameter
      (withHyp hc _) (withHyp hlc _) (withHyp hli _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact InternalAcceptanceBranchProof.successorBranchIntro (guard valid) (.projection 1) (.projection 0)
      candidate z (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))) hg
      (projectionValue 0 (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))))
  obtain ⟨strict⟩ := strict
  obtain ⟨equalCase⟩ := chooseEqual (body := body) (Delta := eqn candidate input :: Delta)
    valid candidate input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction strict)
    (Derivation.implicationIntroduction equalCase)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionChoiceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionChoiceProof
