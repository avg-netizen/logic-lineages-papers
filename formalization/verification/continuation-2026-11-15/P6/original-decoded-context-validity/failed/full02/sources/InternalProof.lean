module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalRawSyntaxTransportInternalVariableSupportProof

theorem tableForward (n : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 (tableGuard n) (numeral 1) raw))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) (numeral (tableListCode n)) raw)) :=
  binaryRecover contains (OriginalRawSyntaxTransport.constant 1 (tableListCode n)) (.projection 0)
    (numeral 1) (numeral (tableListCode n)) raw (Fin.cons raw Fin.elim0) h
    (constantValue (tableListCode n) (Fin.cons raw Fin.elim0)) (projectionValue 0 (Fin.cons raw Fin.elim0))

theorem tableBackward (n : Nat) (raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 contains (numeral 1) (numeral (tableListCode n)) raw))) :
    Nonempty (Derivation body Delta (graph1 (tableGuard n) (numeral 1) raw)) :=
  binaryValue contains (OriginalRawSyntaxTransport.constant 1 (tableListCode n)) (.projection 0)
    (numeral 1) (numeral (tableListCode n)) raw (Fin.cons raw Fin.elim0) h
    (constantValue (tableListCode n) (Fin.cons raw Fin.elim0)) (projectionValue 0 (Fin.cons raw Fin.elim0))

theorem internalContext : Targets.InternalContext := by
  intro n body alpha Delta raw window table hp
  let left : Program 1 := .composition (OriginalDecodedWindowValidity.window n) (fun _ : Fin 1 => InternalUnpair.left)
  let right : Program 1 := .composition (tableGuard n) (fun _ : Fin 1 => InternalUnpair.right)
  constructor
  · intro h
    have hc := conjunctionRecover left right (Fin.cons raw Fin.elim0) h
    have hl := unaryRecover (OriginalDecodedWindowValidity.window n) InternalUnpair.left
      (numeral 1) window (Fin.cons raw Fin.elim0) (andLeft hc) (pairLeft raw window table hp)
    have hr := unaryRecover (tableGuard n) InternalUnpair.right
      (numeral 1) table (Fin.cons raw Fin.elim0) (andRight hc) (pairRight raw window table hp)
    exact andIntro hl (tableForward n table hr)
  · intro h
    have hl := unaryValue (OriginalDecodedWindowValidity.window n) InternalUnpair.left
      (numeral 1) window (Fin.cons raw Fin.elim0) (andLeft h) (pairLeft raw window table hp)
    have hr := unaryValue (tableGuard n) InternalUnpair.right
      (numeral 1) table (Fin.cons raw Fin.elim0) (tableBackward n table (andRight h)) (pairRight raw window table hp)
    exact conjunctionAccept left right (Fin.cons raw Fin.elim0) hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedContextValidity.InternalProof
