module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteHeadArguments.TagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteHeadArguments.BranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261116.OriginalConcreteHeadSignature
open Continuation20261114.OriginalHeadClass.InternalProof (chooseFactor constantTransfer)
attribute [local irreducible] programGraph
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
theorem applicationArguments : Targets.InternalApplicationArguments := by
  intro n arity body alpha Delta raw payload domain result tail out hp hd ht
  obtain ⟨hi⟩ := InternalRecursionClosureLogicProof.closedApply
    (InternalUnpairProof.actualOriginalGeneratedCodeInverse body alpha payload domain result) hd
  have hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left domain payload)) :=
    ⟨Derivation.conjunctionLeft hi⟩
  have htail := binaryValue InternalListCodec.consCode InternalUnpair.left (constant 1 0)
    tail domain z ![payload] ht hl (constantValue 0 ![payload])
  have harrow : Nonempty (Derivation body Delta (graph1 (succOf (.projection 0)) (suc payload) payload)) := unaryValue .succ (.projection 0) (suc payload) payload ![payload]
    (successorValue (Fin.cons payload Fin.elim0)) (projectionValue 0 ![payload])
  have hf := TagProof.internalTagFactor n arity body alpha Delta (4 : Fin 6) raw payload out hp
  constructor
  · intro h
    exact binaryRecover InternalListCodec.consCode (succOf (.projection 0))
      (consOf InternalUnpair.left (constant 1 0)) out (suc payload) tail ![payload]
      (hf.mp h) harrow htail
  · intro h
    exact hf.mpr (binaryValue InternalListCodec.consCode (succOf (.projection 0))
      (consOf InternalUnpair.left (constant 1 0)) out (suc payload) tail ![payload]
      h harrow htail)

theorem rankedArguments : Targets.InternalRankedArguments := by
  intro n arity body alpha Delta raw symbol count out hp hl
  have ha : Nonempty (Derivation body Delta (graph1 (arityAt n arity) count symbol)) :=
    binaryValue InternalRawListRecursion.lookup (.projection 0)
      (constant 1 (NumberedMultisetNumeric.numbersNumber (List.ofFn arity)))
      count symbol (numeral (NumberedMultisetNumeric.numbersNumber (List.ofFn arity))) ![symbol]
      hl (projectionValue 0 ![symbol])
      (constantValue (NumberedMultisetNumeric.numbersNumber (List.ofFn arity)) ![symbol])
  have hf := TagProof.internalTagFactor n arity body alpha Delta (5 : Fin 6) raw symbol out hp
  constructor
  · intro h
    exact unaryRecover groundList (arityAt n arity) out count ![symbol] (hf.mp h) ha
  · intro h
    exact hf.mpr (unaryValue groundList (arityAt n arity) out count ![symbol] h ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteHeadArguments.BranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteHeadArguments.BranchProof
