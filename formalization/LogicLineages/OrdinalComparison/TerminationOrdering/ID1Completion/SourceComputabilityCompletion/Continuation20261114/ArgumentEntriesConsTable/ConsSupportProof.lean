module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesChildren.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationCertificateConstructorsSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem layerCons (raw tau head tail param headValue tailEntries entry listCode answerTail answers : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answerTail (suc tailEntries) z)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answers headValue answerTail))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer (suc (suc listCode)) raw answers param)) := by
  have hd0 := InternalRawListRecursionSupportProof.dropZero (body := body) (Gamma := Delta) answers
  have hd1 := InternalRawListRecursionSupportProof.dropNext answerTail answers z answers hd0
    (InternalRawListRecursionSupportProof.consTail answers headValue answerTail hb)
  have hlookup := InternalRawListRecursionSupportProof.lookupValue (suc tailEntries) (numeral 1) answers answerTail hd1
    (InternalRawListRecursionSupportProof.consHead answerTail (suc tailEntries) z ha)
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons answers Fin.elim0)
  have htail : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.tailAnswer (suc tailEntries) raw answers)) :=
    binaryValue InternalRawListRecursion.lookup (OriginalRawSyntaxTransport.constant 2 1) (.projection 1)
      (suc tailEntries) (numeral 1) answers xs hlookup (constantValue 1 xs) (projectionValue 1 xs)
  have hs := ArgumentEntriesLayer.InternalProof.internalConsSuccess body alpha Delta raw tau head tail tailEntries entry listCode hc he hl
  have hs' := binaryValue ArgumentEntriesLayer.step (.projection 0) ArgumentEntriesLayer.tailAnswer
    (suc listCode) raw (suc tailEntries) xs hs (projectionValue 0 xs) htail
  have hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.recombine (suc (suc listCode)) raw answers)) :=
    unaryValue .succ (.composition ArgumentEntriesLayer.step ![.projection 0,ArgumentEntriesLayer.tailAnswer])
      (suc (suc listCode)) (suc listCode) xs (successorValue (Fin.cons (suc listCode) Fin.elim0)) hs'
  exact binaryValue ArgumentEntriesLayer.recombine (.projection 0) (.projection 1)
    (suc (suc listCode)) raw answers (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))) hr
    (projectionValue 0 (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))))
    (projectionValue 1 (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))))

theorem atLists (raw tau head tail param old headValue tailEntries entry listCode depTail deps answerTail answers : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)))
    (ht : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (hd1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z)))
    (hd0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head depTail)))
    (ha1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answerTail (suc tailEntries) z)))
    (ha0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answers headValue answerTail))) :
    Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param)) := by
  have hchildren := ArgumentEntriesChildren.InternalProof.internalBinary body alpha Delta true raw tau head tail depTail deps hc hd1 hd0
  have hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)) :=
    unaryValue ArgumentEntriesChildren.children (.projection 0) deps raw (Fin.cons raw (Fin.cons param Fin.elim0))
      hchildren (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0)))
  have hmt := MapProof.present body alpha Delta depTail tail z old (suc tailEntries) z answerTail hd1 ht
    (ArgumentEntriesNilExtraction.LeafSupportProof.mapNil old) ha1
  have hm := MapProof.present body alpha Delta deps head depTail old headValue answerTail answers hd0 hh hmt ha0
  exact FinalProof.finalAnswers body alpha Delta ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency
    ArgumentEntriesRecursor.layer raw param raw old deps answers (suc listCode)
    (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0))) ho hd hm
    (layerCons raw tau head tail param headValue tailEntries entry listCode answerTail answers hc he hl ha1 ha0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
