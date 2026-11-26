module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.NilSuppliersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
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
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem nilCache : Targets.InternalNilCache := by
  intro body alpha Delta raw frontier old param table hc ht hm
  have h := ArgumentEntriesNilExtraction.NilSuppliersProof.nilSuppliers body alpha Delta raw z param hc
  exact ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier raw old param z z (numeral 1) table hm (andLeft h)
    (ArgumentEntriesNilExtraction.LeafSupportProof.mapNil old) (andRight h) ht

theorem layerAtTail (raw answers param tailValue inner : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup tailValue (numeral 1) answers)))
    (hi : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step inner raw tailValue))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer (suc inner) raw answers param)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons answers Fin.elim0)
  have hc : Nonempty (Derivation body Delta (programGraph (OriginalRawSyntaxTransport.constant 2 1) (numeral 1) xs)) :=
    OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs
  have ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.tailAnswer tailValue raw answers)) :=
    binaryValue InternalRawListRecursion.lookup (OriginalRawSyntaxTransport.constant 2 1) (.projection 1)
      tailValue (numeral 1) answers xs hl hc (projectionValue 1 xs)
  have hs : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner raw answers)) :=
    binaryValue ArgumentEntriesLayer.step ArgumentEntriesLayer.raw ArgumentEntriesLayer.tailAnswer inner raw tailValue xs
      hi (projectionValue 0 xs) ht
  exact ArgumentEntriesTableDomain.SupportProof.layerSome raw answers param inner hs
theorem atValues (raw tau head tail param frontier1 frontier2 old1 old2 table1 table2 left1 left2 tailValue found deps answers1 answers2 inner : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hs1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table1 frontier1 old1 param)))
    (hs2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table2 frontier2 old2 param)))
    (hm1 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier1 raw)))
    (hm2 : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier2 raw)))
    (hh1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left1) old1 head)))
    (hh2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left2) old2 head)))
    (ht1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old1 tail)))
    (ht2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc tailValue) old2 tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table1 raw)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers1 deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers2 deps old2)))
    (hi : Nonempty (Derivation body Delta (graph2 ArgumentEntriesLayer.step inner raw tailValue))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table2 raw)) := by
  have hp1 := (ArgumentEntriesOrderedAnswers.Proof.consAnswers body alpha Delta raw tau head tail param deps old1 left1 tailValue answers1 hc hd hh1 ht1 ha1).2
  have hp2 := (ArgumentEntriesOrderedAnswers.Proof.consAnswers body alpha Delta raw tau head tail param deps old2 left2 tailValue answers2 hc hd hh2 ht2 ha2).2
  have hg1 := layerAtTail raw answers1 param tailValue inner hp1 hi
  have hg2 := layerAtTail raw answers2 param tailValue inner hp2 hi
  have h1 := ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier1 raw old1 param deps answers1 inner table1 hm1 hd ha1 hg1 hs1
  have h2 := ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier2 raw old2 param deps answers2 inner table2 hm2 hd ha2 hg2 hs2
  have he := valueUnique ExchangeMapGraph.lookup (suc inner) found (Fin.cons table1 (Fin.cons raw Fin.elim0)) h1 hl
  exact outputTransport ExchangeMapGraph.lookup (suc inner) found (Fin.cons table2 (Fin.cons raw Fin.elim0)) he h2

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.SupportProof
