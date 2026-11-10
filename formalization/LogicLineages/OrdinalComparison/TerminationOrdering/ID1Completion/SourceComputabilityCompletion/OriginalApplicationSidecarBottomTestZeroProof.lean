module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberPathDispatchSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual queried same-type bottom candidate cannot equal input when
bottomTest rejects at one. Internal equality rejection gives literal zero. -/
theorem zeroAtCandidate (input candidate : OrdinaryArithmetic.Term alpha)
    (hq : Nonempty (Derivation body Delta
      (programGraph (.composition BottomRepresentative.bottomCode
        (fun _ : Fin 1 => leftOf (.projection 0))) candidate (Fin.cons input Fin.elim0))))
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) input).not)) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph z input)) := by
  let q : Program 1 := .composition BottomRepresentative.bottomCode
    (fun _ : Fin 1 => leftOf (.projection 0))
  let xs : Fin 1 → OrdinaryArithmetic.Term alpha := Fin.cons input Fin.elim0
  have hneq : Nonempty (Derivation body Delta (eqn input candidate).not) := by
    let E := eqn input candidate
    have hp := outputTransport (.projection (0 : Fin 1)) input candidate xs
      (show Nonempty (Derivation body (E :: Delta) E) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (projectionValue 0 xs)
    obtain ⟨accepted⟩ := InternalApplicationStepPeelSupportProof.sameAccept (.projection 0) q
      candidate xs hp (withHyp hq E)
    obtain ⟨rejected⟩ := withHyp hn E
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination rejected accepted)⟩
  exact InternalApplicationCertificateConstructorsSupportProof.binaryValue InternalEqualityTest.equalityTest (.projection 0) q z input candidate xs
    (InternalOriginalObjectFiberPathDispatchSupportProof.equalityOfNonmatch input candidate hneq)
    (projectionValue 0 xs) hq

/-- Eliminate an internal query of the actual bottom candidate. This is a
law of the literal bottomTest, without a Boolean-range or normalization premise. -/
theorem zeroOfNonacceptance (input : OrdinaryArithmetic.Term alpha)
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) input).not)) :
    Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph z input)) := by
  apply programCases (.composition BottomRepresentative.bottomCode
    (fun _ : Fin 1 => leftOf (.projection 0))) (Fin.cons input Fin.elim0) _
  intro beta j Theta candidate hj hq
  simp only [BottomRepresentative.bottomGraph,graph1Rename,zRelabel]
  have hn' := renameInto hn j Theta hj
  rw [BottomApplicationProof.notBottomRename] at hn'
  simp only [consTermRename,emptyRename] at hq
  exact zeroAtCandidate (input.relabel j) candidate hq hn'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarBottomTestZeroProof
