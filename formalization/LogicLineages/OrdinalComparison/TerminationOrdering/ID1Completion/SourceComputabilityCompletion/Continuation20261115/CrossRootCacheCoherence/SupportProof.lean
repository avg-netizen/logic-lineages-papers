module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.FrontierCapacity.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTailCoherence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNonConsCoherence.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem stage (index seed param depth frontier table old : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)))
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old index seed param))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)) := by
  have hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.rank seed seed param)) :=
    projectionValue 0 (Fin.cons seed (Fin.cons param Fin.elim0))
  exact (ExchangeGraphRecursion.InternalProof.internalSuccessor body alpha Delta
    ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    index seed param old seed depth frontier table ho hr hd hf).mp ht

theorem predecessorBound (index seed : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded (suc index) seed))) :
    Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)) := by
  have hw := PrimaryUncoveredCount.OrderProof.strictNext (suc index) seed hb
  have hn := InternalCoprimeMultipleBoundedProof.selfLtSucc (body := body) (Gamma := Delta) index
  obtain ⟨h⟩ := strictWeakTrans index (suc index) seed hn hw
  exact ⟨InternalQuotientComparisonProof.orLeft h⟩

theorem consTailStrict (raw tau head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess tail raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  have hp := projectionValue (body := body) (Gamma := Delta) (0 : Fin 1) xs
  have ha := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consArity (.projection 0) raw tau head tail xs hp hc
  have hh := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consFirst (.projection 0) raw tau head tail xs hp hc
  have ht := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consSecond (.projection 0) raw tau head tail xs hp hc
  exact andRight (OriginalRawSyntaxTransportInternalConstructorBoundsProof.binaryChildrenStrict raw head tail ha hh ht)

theorem indexNonzero (raw tail index : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess tail raw)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded raw index))) :
    Nonempty (Derivation body Delta (eqn index z).not) := by
  have hw := PrimaryUncoveredCount.OrderProof.strictNext raw index hb
  obtain ⟨h⟩ := strictWeakTrans tail raw index hl hw
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  have h0 := orderRight tail (Derivation.hypothesis (body := body) (Gamma := eqn index z :: Delta) List.mem_cons_self)
    (InternalSourceInversionSupportProof.addHyp h _)
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha tail
  exact Derivation.implicationElimination (weakenClosed hn _) h0

theorem memberTail (code head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail needle))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) code needle)) := by
  apply formulaCases (equal head needle)
  · exact containsHit code head tail needle (withHyp hc _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact containsMiss code head tail needle (numeral 1) (withHyp hc _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hm _)

theorem dependencyAtLists (raw tau head tail param rest deps : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest tail z)))
    (hd : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps head rest))) :
    Nonempty (Derivation body Delta
      (graph2 ArgumentEntriesRecursor.dependency deps raw param ⊓
       (graph2 contains (numeral 1) deps head ⊓ graph2 contains (numeral 1) deps tail))) := by
  have hc' := ArgumentEntriesChildren.InternalProof.internalBinary body alpha Delta true raw tau head tail rest deps hc hr hd
  have hdep : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)) :=
    unaryValue ArgumentEntriesChildren.children (.projection 0) deps raw (Fin.cons raw (Fin.cons param Fin.elim0))
      hc' (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0)))
  have heh : Nonempty (Derivation body Delta (equal head head)) := by rw [equalEqn]; exact ⟨refl head⟩
  have het : Nonempty (Derivation body Delta (equal tail tail)) := by rw [equalEqn]; exact ⟨refl tail⟩
  exact andIntro hdep (andIntro (containsHit deps head rest head hd heh)
    (memberTail deps head rest tail hd (containsHit rest tail z tail hr het)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.CrossRootCacheCoherence.SupportProof
