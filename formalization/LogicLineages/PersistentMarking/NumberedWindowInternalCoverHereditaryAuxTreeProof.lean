module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTreeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalAuxMeasureOpenDataProof (bothChildBounds)
open NumberedWindowInternalCoverHereditaryAuxTargets

theorem forkFromPhysicalKey {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (dom cod fn arg : OTerm α) (first : HereditaryAuxTree body Γ fn) (second : HereditaryAuxTree body Γ arg) :
    HereditaryAuxTree body Γ (auxiliaryTerm dom cod fn arg) := by
  have earlier := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  exact .fork dom cod fn arg earlier.1 earlier.2 first second

theorem treeRenameInto {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    {q : OTerm α} (j : α → β) (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (tree : HereditaryAuxTree body Γ q) : HereditaryAuxTree body Δ (q.relabel j) := by
  induction tree with
  | terminal prior noLambda noAux =>
    rw [sucRelabel]
    have h := renameInto noLambda j Δ keep
    have a := renameInto noAux j Δ keep
    simp only [unaryRename,sucRelabel,zRelabel] at h a
    exact .terminal (prior.relabel j) h a
  | fork dom cod fn arg h0 h1 _ _ first second =>
    rw [auxiliaryRename]
    have leftEarlier := renameInto h0 j Δ keep
    have rightEarlier := renameInto h1 j Δ keep
    simp only [orderRename,auxiliaryRename] at leftEarlier rightEarlier
    exact .fork (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
      leftEarlier rightEarlier first second

#print axioms forkFromPhysicalKey
#print axioms treeRenameInto

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHereditaryAuxTreeProof
