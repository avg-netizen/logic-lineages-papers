module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import Mathlib.Tactic.FinCases
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransport (constant)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalAcceptanceBranchProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open InternalTagArithmeticSyntaxProof (z suc)
theorem nilTag (value tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value (numeral 6) (numeral 0)))) :
    Nonempty (Derivation body Delta (programGraph (leftOf raw) (numeral 6) ![value,tail])) := by
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha value (numeral 6) (numeral 0)) hp
  exact unaryValue InternalUnpair.left raw (numeral 6) value ![value,tail]
    ⟨Derivation.conjunctionLeft hi⟩ (projectionValue 0 ![value,tail])

theorem internalNil : Targets.InternalNil := by
  intro body alpha Delta value tail hp
  apply branchNumeralIntro 6 6 (leftOf raw) _ _ (numeral 1) ![value,tail] (nilTag value tail hp)
  exact constantValue 1 ![value,tail]

theorem internalConsFailure : Targets.InternalConsFailure := by
  intro body alpha Delta value tau q rest hc
  let xs : Fin 2 → OTerm alpha := ![value,numeral 0]
  have ht := consTag raw value tau q rest xs (projectionValue 0 xs) hc
  apply branchNumeralIntro 7 6 (leftOf raw) _ _ (numeral 0) xs ht
  apply branchNumeralIntro 7 7 (leftOf raw) _ _ (numeral 0) xs ht
  exact zeroBranchIntro tailOption (constant 2 0) (OriginalRawSyntaxTransport.succOf prepend)
    (numeral 0) xs (projectionValue 1 xs) (constantValue 0 xs)

theorem internalConsSuccess : Targets.InternalConsSuccess := by
  intro body alpha Delta value tau q rest tail entryCode listCode hc he hl
  let xs : Fin 2 → OTerm alpha := ![value,suc tail]
  have hq : Nonempty (Derivation body Delta (programGraph raw value xs)) := projectionValue 0 xs
  have ht := consTag raw value tau q rest xs hq hc
  have ha := consType raw value tau q rest xs hq hc
  have hchild := consHead raw value tau q rest xs hq hc
  have hent : Nonempty (Derivation body Delta (programGraph entry entryCode xs)) :=
    binaryValue InternalPairing.pairing annotation child entryCode tau q xs he ha hchild
  have htail : Nonempty (Derivation body Delta (programGraph tailList tail xs)) :=
    unaryValue InternalEqualityTest.predecessor tailOption tail (suc tail) xs
      (InternalEqualityTestPredecessorProof.predecessorSuccessor tail) (projectionValue 1 xs)
  have hlist : Nonempty (Derivation body Delta (programGraph prepend listCode xs)) :=
    binaryValue InternalListCodec.consCode entry tailList listCode entryCode tail xs hl hent htail
  have hsucc : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.succOf prepend) (suc listCode) xs)) :=
    unaryValue .succ prepend (suc listCode) listCode xs (successorValue ![listCode]) hlist
  apply branchNumeralIntro 7 6 (leftOf raw) _ _ (suc listCode) xs ht
  apply branchNumeralIntro 7 7 (leftOf raw) _ _ (suc listCode) xs ht
  exact successorBranchIntro tailOption (constant 2 0) (OriginalRawSyntaxTransport.succOf prepend)
    (suc listCode) tail xs (projectionValue 1 xs) hsucc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
