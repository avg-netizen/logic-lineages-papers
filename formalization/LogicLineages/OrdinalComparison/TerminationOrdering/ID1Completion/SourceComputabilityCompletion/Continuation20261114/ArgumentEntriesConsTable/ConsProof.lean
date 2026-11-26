module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsProof
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
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

theorem atAnswers (raw tau head tail param old headValue tailEntries entry listCode depTail deps answerTail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)))
    (ht : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (hd1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z)))
    (hd0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head depTail)))
    (ha1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode answerTail (suc tailEntries) z)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons headValue (Fin.cons answerTail Fin.elim0)) _
  intro beta j Theta answers hj hx
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hhj := renameInto hh j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hhj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at htj
  have hej := renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hej
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  have hd1j := renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hd1j
  have hd0j := renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hd0j
  have ha1j := renameInto ha1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ha1j
  exact ConsSupportProof.atLists (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (old.relabel j) (headValue.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) (depTail.relabel j) (deps.relabel j) (answerTail.relabel j) answers hcj hoj hhj htj hej hlj hd1j hd0j ha1j hx

theorem atAnswerTail (raw tau head tail param old headValue tailEntries entry listCode depTail deps : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)))
    (ht : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (hd1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z)))
    (hd0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head depTail)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons (suc tailEntries) (Fin.cons z Fin.elim0)) _
  intro beta j Theta answerTail hj hx
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hhj := renameInto hh j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hhj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at htj
  have hej := renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hej
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  have hd1j := renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hd1j
  have hd0j := renameInto hd0 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hd0j
  exact atAnswers (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (old.relabel j) (headValue.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) (depTail.relabel j) (deps.relabel j) answerTail hcj hoj hhj htj hej hlj hd1j hd0j hx

theorem atDeps (raw tau head tail param old headValue tailEntries entry listCode depTail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)))
    (ht : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    (hd1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons depTail Fin.elim0)) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hhj := renameInto hh j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hhj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at htj
  have hej := renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hej
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  have hd1j := renameInto hd1 j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hd1j
  exact atAnswerTail (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (old.relabel j) (headValue.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) (depTail.relabel j) deps hcj hoj hhj htj hej hlj hd1j hx

theorem atDepTail (raw tau head tail param old headValue tailEntries entry listCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hh : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc headValue) old head)))
    (ht : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc (suc tailEntries)) old tail)))
    (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry tau head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entry tailEntries)))
    : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc listCode) raw param)) := by
  apply programCases InternalListCodec.consCode (Fin.cons tail (Fin.cons z Fin.elim0)) _
  intro beta j Theta depTail hj hx
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  simp only [graph2Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hoj
  have hhj := renameInto hh j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hhj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at htj
  have hej := renameInto he j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hej
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  exact atDeps (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (old.relabel j) (headValue.relabel j) (tailEntries.relabel j) (entry.relabel j) (listCode.relabel j) depTail hcj hoj hhj htj hej hlj hx

theorem consTable : Targets.InternalConsTable := by
  intro body alpha Delta raw tau head tail param old headValue tailEntries entry listCode hc ho hh ht he hl
  exact atDepTail raw tau head tail param old headValue tailEntries entry listCode hc ho hh ht he hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsProof
