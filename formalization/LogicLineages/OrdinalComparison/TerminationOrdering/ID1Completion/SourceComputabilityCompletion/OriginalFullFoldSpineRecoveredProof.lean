module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineRecoveredProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine OriginalFullFoldSpineSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityClosure (applicationConstructors)
open InternalControlGraphSupportProof (emptyRename)
open InternalAcceptanceSupportProof (programCases)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof (certifiedOutputRename sourcePremisesRename)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem recoveredRename {beta : Type} (data : Data)
    (arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter :
      OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (OriginalCanonicalApplicationInversionTargets.Recovered data
      arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter).relabel j =
      OriginalCanonicalApplicationInversionTargets.Recovered data
        (arrow.relabel j) (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
        (fn.relabel j) (arg.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
        (rebuilt.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) := by
  simp only [OriginalCanonicalApplicationInversionTargets.Recovered,applicationConstructors,
    conjunctionRename,graph2Rename,graph4Rename,certifiedOutputRename,sourcePremisesRename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

/-- Bind the original function's WHOLE mark by Program totality, retaining
every recovered constructor, certified output and final selected leaf. -/
theorem withMark (base : Data) (window : Program 1)
    (q input typ out parameter mark payload arrow d e fp ap fn arg functionOut argumentOut rebuilt :
      OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Gamma
      (belowPayload (SpineApplicationTargets.selectedData base window) window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma
      (premises (SpineApplicationTargets.selectedData base window) window out input typ parameter)))
    (hpr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp fn)))
    (hfl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess fp payload)))
    (hrecovered : Nonempty (Derivation body Gamma
      (OriginalCanonicalApplicationInversionTargets.Recovered
        (SpineApplicationTargets.selectedData base window)
        arrow d e fp ap fn arg functionOut argumentOut rebuilt input out parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  apply programCases BottomSpineMeasure.measure (Fin.cons fn Fin.elim0) _
  intro beta j Delta fm hinc hfm
  rw [conclusionRename]
  simp only [consTermRename,emptyRename] at hfm
  have hb' := renameInto hb j Delta hinc
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hinc
  have hpr' := renameInto hpr j Delta hinc
  have hfr' := renameInto hfr j Delta hinc
  rw [graph1Rename] at hr' hpr' hfr'
  have hp' := renameInto hp j Delta hinc
  rw [premisesRename] at hp'
  have hfl' := renameInto hfl j Delta hinc
  unfold InternalLessThan.strictLess at hfl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl'
  have hrecovered' := renameInto hrecovered j Delta hinc
  rw [recoveredRename] at hrecovered'
  exact OriginalFullFoldSpineApplicationProof.atRecoveredMark base window
    (q.relabel j) (input.relabel j) (typ.relabel j) (out.relabel j) (parameter.relabel j)
    (mark.relabel j) (payload.relabel j) (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j)
    (functionOut.relabel j) (argumentOut.relabel j) (rebuilt.relabel j) fm
    hb' hr' hp' hpr' hfr' hfl' hrecovered' hfm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineRecoveredProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineRecoveredProof
