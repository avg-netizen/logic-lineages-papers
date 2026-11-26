module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import Mathlib.Tactic.FinCases
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.InternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
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
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
theorem unaryList (value child listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf raw) (numeral 1) value)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf raw) child value)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode child (numeral 0)))) :
    Nonempty (Derivation body Delta (graph1 children listCode value)) := by
  let xs : Fin 1 → OTerm alpha := ![value]
  apply successorBranchIntro (OriginalRawSyntaxTransport.arityOf raw) (constant 1 0) _ listCode z xs ha
  apply branchNumeralIntro 1 2 (OriginalRawSyntaxTransport.arityOf raw) singleton double listCode xs ha
  exact binaryValue InternalListCodec.consCode (OriginalRawSyntaxTransport.firstOf raw) (constant 1 0)
    listCode child (numeral 0) xs hc hf (constantValue 0 xs)

theorem binaryList (value left right rest listCode : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf raw) (numeral 2) value)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf raw) left value)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf raw) right value)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right (numeral 0))))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode left rest))) :
    Nonempty (Derivation body Delta (graph1 children listCode value)) := by
  let xs : Fin 1 → OTerm alpha := ![value]
  apply successorBranchIntro (OriginalRawSyntaxTransport.arityOf raw) (constant 1 0) _ listCode (numeral 1) xs ha
  apply branchNumeralIntro 2 2 (OriginalRawSyntaxTransport.arityOf raw) singleton double listCode xs ha
  have hrest := binaryValue InternalListCodec.consCode (OriginalRawSyntaxTransport.secondOf raw) (constant 1 0)
    rest right (numeral 0) xs hr hs (constantValue 0 xs)
  exact binaryValue InternalListCodec.consCode (OriginalRawSyntaxTransport.firstOf raw)
    (consOf (OriginalRawSyntaxTransport.secondOf raw) (constant 1 0)) listCode left rest xs hc hf hrest

theorem internalUnary : Targets.InternalUnary := by
  intro body alpha Delta ordinary value metadata child listCode hc hl
  let xs : Fin 1 → OTerm alpha := ![value]
  have hq : Nonempty (Derivation body Delta (programGraph raw value xs)) := projectionValue 0 xs
  cases ordinary with
  | false => exact unaryList value child listCode
      (lambdaArity raw value metadata child xs hq hc) (lambdaFirst raw value metadata child xs hq hc) hl
  | true => exact unaryList value child listCode
      (ordinaryArity raw value metadata child xs hq hc) (ordinaryFirst raw value metadata child xs hq hc) hl

theorem internalBinary : Targets.InternalBinary := by
  intro body alpha Delta cons value tau left right rest listCode hc hr hl
  let xs : Fin 1 → OTerm alpha := ![value]
  have hq : Nonempty (Derivation body Delta (programGraph raw value xs)) := projectionValue 0 xs
  cases cons with
  | false => exact binaryList value left right rest listCode
      (applicationArity raw value tau left right xs hq hc)
      (applicationFirst raw value tau left right xs hq hc)
      (applicationSecond raw value tau left right xs hq hc) hr hl
  | true => exact binaryList value left right rest listCode
      (consArity raw value tau left right xs hq hc)
      (consFirst raw value tau left right xs hq hc)
      (consSecond raw value tau left right xs hq hc) hr hl

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta value k hd tau base ts extras rest listCode hc hr hl
  let xs : Fin 1 → OTerm alpha := ![value]
  have hq : Nonempty (Derivation body Delta (programGraph raw value xs)) := projectionValue 0 xs
  exact binaryList value base extras rest listCode
    (numberedArity raw value k hd tau base ts extras xs hq hc)
    (numberedFirst raw value k hd tau base ts extras xs hq hc)
    (numberedSecond raw value k hd tau base ts extras xs hq hc) hr hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
