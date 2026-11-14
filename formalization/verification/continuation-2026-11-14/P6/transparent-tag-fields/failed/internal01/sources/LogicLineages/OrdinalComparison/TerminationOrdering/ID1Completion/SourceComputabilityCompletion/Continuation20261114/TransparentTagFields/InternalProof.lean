module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem internalTags : Targets.InternalTags := by
  intro body alpha Delta V node code param source target st sp tt tp hV hn hs ht
  obtain ⟨hn⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha node source target) hn
  obtain ⟨hs⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha source st sp) hs
  obtain ⟨ht⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha target tt tp) ht
  let v : Fin 3 → OTerm alpha := ![node,code,param]
  have hsource : Nonempty (Derivation body Delta (programGraph sourceCode source v)) :=
    unaryValue InternalUnpair.left (.projection 0) source node v
      ⟨Derivation.conjunctionLeft hn⟩ (projectionValue 0 v)
  have htarget : Nonempty (Derivation body Delta (programGraph targetCode target v)) :=
    unaryValue InternalUnpair.right (.projection 0) target node v
      ⟨Derivation.conjunctionRight hn⟩ (projectionValue 0 v)
  have hst : Nonempty (Derivation body Delta (programGraph sourceRawTag st v)) :=
    unaryValue InternalUnpair.left sourceCode st source v ⟨Derivation.conjunctionLeft hs⟩ hsource
  have htt : Nonempty (Derivation body Delta (programGraph targetRawTag tt v)) :=
    unaryValue InternalUnpair.left targetCode tt target v ⟨Derivation.conjunctionLeft ht⟩ htarget
  exact ⟨successorBranchIntro V (InternalAcceptance.constantZero 3) sourceRawTag st z v hV hst,
    successorBranchIntro V (InternalAcceptance.constantZero 3) targetRawTag tt z v hV htt⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
