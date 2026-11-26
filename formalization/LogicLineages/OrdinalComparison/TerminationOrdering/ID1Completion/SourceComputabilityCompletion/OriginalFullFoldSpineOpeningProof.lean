module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineRecoveredProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineOpeningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine OriginalFullFoldSpineSyntaxProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Open the original root and internally recover both actual child folds.
The strict function-payload bound is retained across both CPS scopes. -/
theorem acceptedAtOutput (base : Data) (window : Program 1)
    (q input typ out parameter mark : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Gamma
      (belowPayload (SpineApplicationTargets.selectedData base window) window q)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right q input)))
    (hp : Nonempty (Derivation body Gamma
      (premises (SpineApplicationTargets.selectedData base window) window out input typ parameter)))
    (hg : Nonempty (Derivation body Gamma
      (graph2 (InternalParameterizedApplicationResultStack.openGuardP
        (InternalParameterizedCanonicalResultFold.rootGuard
          (SpineApplicationTargets.selectedData base window))) (suc z) input parameter))) :
    Nonempty (Derivation body Gamma (conclusion out input mark)) := by
  let data := SpineApplicationTargets.selectedData base window
  apply InternalParameterizedApplicationResultFoldTotalityOpeningProof.openingCases
    (InternalParameterizedCanonicalResultFold.rootGuard data) input parameter _ hg
  intro beta j Delta payload arrow d e fp ap fn arg hinc hc hpr hfr _ hfl _ _
  rw [conclusionRename]
  have hb' := renameInto hb j Delta hinc
  rw [belowPayloadRename] at hb'
  have hr' := renameInto hr j Delta hinc
  rw [graph1Rename] at hr'
  have hp' := renameInto hp j Delta hinc
  rw [premisesRename] at hp'
  apply OriginalCanonicalApplicationInversionProof.atConstructors data
    arrow d e fp ap fn arg (input.relabel j) (out.relabel j) (parameter.relabel j) _
    hc (andLeft (andLeft (andRight hp'))) (andRight (andRight hp'))
  intro gamma k Theta hk functionOut argumentOut rebuilt hrecovered
  rw [conclusionRename]
  have hb'' := renameInto hb' k Theta hk
  rw [belowPayloadRename] at hb''
  have hr'' := renameInto hr' k Theta hk
  have hpr' := renameInto hpr k Theta hk
  have hfr' := renameInto hfr k Theta hk
  rw [graph1Rename] at hr'' hpr' hfr'
  have hp'' := renameInto hp' k Theta hk
  rw [premisesRename] at hp''
  have hfl' := renameInto hfl k Theta hk
  unfold InternalLessThan.strictLess at hfl'
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hfl'
  exact OriginalFullFoldSpineRecoveredProof.withMark base window
    ((q.relabel j).relabel k) ((input.relabel j).relabel k) ((typ.relabel j).relabel k)
    ((out.relabel j).relabel k) ((parameter.relabel j).relabel k) ((mark.relabel j).relabel k)
    (payload.relabel k) (arrow.relabel k) (d.relabel k) (e.relabel k)
    (fp.relabel k) (ap.relabel k) (fn.relabel k) (arg.relabel k)
    functionOut argumentOut rebuilt hb'' hr'' hp'' hpr' hfr' hfl' hrecovered

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineOpeningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineOpeningProof
