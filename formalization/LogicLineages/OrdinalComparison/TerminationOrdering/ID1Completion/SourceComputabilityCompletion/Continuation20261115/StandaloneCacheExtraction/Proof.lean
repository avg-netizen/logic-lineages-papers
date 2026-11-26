module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SupportProof

theorem atRoot (raw param index seed depth frontier table value root nodes : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)))
    (hr : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph root (suc raw) raw param)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    : Nonempty (Derivation body Delta (SupportProof.relation raw param table value)) := by
  have hb0 := PrimaryUncoveredCount.OrderProof.reflexive (body := body) (Delta := Delta) raw
  have hs0 := InternalEqualityTestSubtractionProof.subtractSelf (body := body) (Gamma := Delta) raw
  have hf0 := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero ArgumentEntriesRecursor.dependency raw param nodes hn
  have hm0 := containsHit nodes raw z raw hn (by simpa only [InternalControlGraphSupportProof.equalEqn] using (Nonempty.intro (refl raw) : Nonempty (Derivation body Delta (eqn raw raw))))
  apply andIntro
  · let E := graph2 ArgumentEntriesRecursor.extract value raw param
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl := (RootProof.rootExtraction body alpha (E :: Delta) raw param root value (withHyp hr E)).mp he
    obtain ⟨hout⟩ := CrossRootCacheCoherence.Proof.cacheTransport body alpha (E :: Delta)
      raw param raw raw z nodes root index seed depth frontier table (suc value)
      (withHyp hb0 E) (withHyp hs0 E) (withHyp hf0 E) (withHyp hm0 E) (withHyp hr E)
      (withHyp hb E) (withHyp hs E) (withHyp hf E) (withHyp hm E) (withHyp ht E) hl
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let L := graph2 ExchangeMapGraph.lookup (suc value) table raw
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hroot := CrossRootCacheCoherence.Proof.cacheTransport body alpha (L :: Delta)
      raw param index seed depth frontier table raw raw z nodes root (suc value)
      (withHyp hb L) (withHyp hs L) (withHyp hf L) (withHyp hm L) (withHyp ht L)
      (withHyp hb0 L) (withHyp hs0 L) (withHyp hf0 L) (withHyp hm0 L) (withHyp hr L) hl
    obtain ⟨hout⟩ := (RootProof.rootExtraction body alpha (L :: Delta) raw param root value (withHyp hr L)).mpr hroot
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem at1 (raw param index seed depth frontier table value root : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)))
    (hroot : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph root (suc raw) raw param)))
    : Nonempty (Derivation body Delta (SupportProof.relation raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons raw (Fin.cons z (Fin.elim0))) _
  intro beta j Theta nodes hj hx
  rw [SupportProof.relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hbj := renameInto hb j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hsj := renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hsj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hmj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at htj
  have hrootj := renameInto hroot j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hrootj
  exact atRoot (raw.relabel j) (param.relabel j) (index.relabel j) (seed.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j) (value.relabel j) (root.relabel j) nodes hbj hsj hfj hmj htj hrootj hx

theorem at0 (raw param index seed depth frontier table value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index seed)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index seed)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc index) seed param)))
    : Nonempty (Derivation body Delta (SupportProof.relation raw param table value)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons (suc raw) (Fin.cons raw (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta root hj hx
  rw [SupportProof.relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hbj := renameInto hb j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hsj := renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hsj
  have hfj := renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hmj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at htj
  exact at1 (raw.relabel j) (param.relabel j) (index.relabel j) (seed.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j) (value.relabel j) root hbj hsj hfj hmj htj hx

theorem alignedExtraction : Targets.InternalAlignedExtraction := by
  intro body alpha Delta raw param index seed depth frontier table value hb hs hf hm ht
  have h := at0 raw param index seed depth frontier table value hb hs hf hm ht
  constructor
  · intro he
    obtain ⟨hi⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
  · intro hl
    obtain ⟨hi⟩ := andRight h
    obtain ⟨hl⟩ := hl
    exact ⟨Derivation.implicationElimination hi hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.Proof
