module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowSlotProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (projectionValue outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (zeroAccept)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename makeUnary)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverRestrictedListWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualRestrictedArgument (G : Program 1) (i : Nat) (raw a : OTerm α)
    (selector : Nonempty (Derivation body Γ (unary (field i) a raw)))
    (positive : Nonempty (Derivation body Γ (unary (listSlotAllowed G i) (suc z) raw))) :
    Nonempty (Derivation body Γ (unary (argumentReject G) z a)) := by
  let J := argumentReject G
  let Z := LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest
  let Q := unary J z a
  apply programCases J ![a] Q
  intro β j Δ m keep actual
  rw [inputsRename] at actual
  have select := renameInto selector j Δ keep
  have accepts := renameInto positive j Δ keep
  rw [unaryRename] at select
  simp only [unaryRename,sucRelabel,zRelabel] at accepts
  let a' := a.relabel j
  let raw' := raw.relabel j
  have took := makeUnary J (field i) m raw' a' actual select
  have checked : Nonempty (Derivation body Δ (unary Z (suc z) m)) := by
    apply compositionRecover Z (fun _ : Fin 1 => applyUnary J (field i)) (suc z) ![raw'] ![m] accepts
    intro k
    obtain rfl := Fin.eq_zero k
    exact took
  have eq := zeroAccept m checked
  simp only [Q,unaryRename,zRelabel]
  exact outputTransport J m z ![a'] eq actual

theorem unliftListGuard (P : Program 1) (ctx raw : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (onRaw P) (suc z) ![ctx,raw]))) :
    Nonempty (Derivation body Γ (unary P (suc z) raw)) := by
  apply compositionRecover P (fun _ : Fin 1 => Program.projection 1) (suc z) ![ctx,raw] ![raw] actual
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![ctx,raw]

#print axioms actualRestrictedArgument
#print axioms unliftListGuard

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowSlotProof
