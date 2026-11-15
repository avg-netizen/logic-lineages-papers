module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Extraction.RootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Extraction.Proof
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

variable (n : Nat)
theorem atRoot (raw param index seed rank depth frontier table value ownrank root nodes : OTerm alpha)
    (hseed : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index rank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) table (suc index) seed param)))
    (hownrank : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R ownrank raw param)))
    (hroot : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) root (suc ownrank) raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    : Nonempty (Derivation body Delta (SupportProof.relation n raw param table value)) := by
  have hb0 := PrimaryUncoveredCount.OrderProof.reflexive (body := body) (Delta := Delta) ownrank
  have hs0 := InternalEqualityTestSubtractionProof.subtractSelf (body := body) (Gamma := Delta) ownrank
  have hf0 := ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero OriginalEnumerationRecursionInterface.D raw param nodes hnodes
  have hm0 := containsHit nodes raw z raw hnodes (by simpa only [InternalControlGraphSupportProof.equalEqn] using (Nonempty.intro (refl raw) : Nonempty (Derivation body Delta (eqn raw raw))))
  apply andIntro
  · let E := graph2 (ExchangeSelectedRecursor.exchange OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) value raw param
    have he : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl := (RootProof.rootExtraction n body alpha (E :: Delta) raw param ownrank root value (withHyp hownrank E) (withHyp hroot E)).mp he
    obtain ⟨hout⟩ := OriginalEnumerationCacheCoherence.Proof.transport n body alpha (E :: Delta)
      raw param ownrank raw ownrank z nodes root index seed rank depth frontier table (suc value)
      (withHyp hownrank E) (withHyp hb0 E) (withHyp hs0 E) (withHyp hf0 E) (withHyp hm0 E) (withHyp hroot E)
      (withHyp hseed E) (withHyp hb E) (withHyp hs E) (withHyp hf E) (withHyp hm E) (withHyp ht E) hl
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let L := graph2 ExchangeMapGraph.lookup (suc value) table raw
    have hl : Nonempty (Derivation body (L :: Delta) L) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hrootLookup := OriginalEnumerationCacheCoherence.Proof.transport n body alpha (L :: Delta)
      raw param index seed rank depth frontier table ownrank raw ownrank z nodes root (suc value)
      (withHyp hseed L) (withHyp hb L) (withHyp hs L) (withHyp hf L) (withHyp hm L) (withHyp ht L)
      (withHyp hownrank L) (withHyp hb0 L) (withHyp hs0 L) (withHyp hf0 L) (withHyp hm0 L) (withHyp hroot L) hl
    obtain ⟨hout⟩ := (RootProof.rootExtraction n body alpha (L :: Delta) raw param ownrank root value (withHyp hownrank L) (withHyp hroot L)).mpr hrootLookup
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem at2 (raw param index seed rank depth frontier table value ownrank root : OTerm alpha)
    (hseed : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index rank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) table (suc index) seed param)))
    (hownrank : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R ownrank raw param)))
    (hroot : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) root (suc ownrank) raw param)))
    : Nonempty (Derivation body Delta (SupportProof.relation n raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons raw (Fin.cons z Fin.elim0)) _
  intro beta j Theta nodes hj hx
  rw [SupportProof.relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hseedj := InternalGraphCompositionFunctionalityProof.renameInto hseed j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hseedj
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hsj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hmj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at htj
  have hownrankj := InternalGraphCompositionFunctionalityProof.renameInto hownrank j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hownrankj
  have hrootj := InternalGraphCompositionFunctionalityProof.renameInto hroot j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hrootj
  exact atRoot n (raw.relabel j) (param.relabel j) (index.relabel j) (seed.relabel j) (rank.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j) (value.relabel j) (ownrank.relabel j) (root.relabel j) nodes hseedj hbj hsj hfj hmj htj hownrankj hrootj hx

theorem at1 (raw param index seed rank depth frontier table value ownrank : OTerm alpha)
    (hseed : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index rank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) table (suc index) seed param)))
    (hownrank : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R ownrank raw param)))
    : Nonempty (Derivation body Delta (SupportProof.relation n raw param table value)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) (Fin.cons (suc ownrank) (Fin.cons raw (Fin.cons param Fin.elim0))) _
  intro beta j Theta root hj hx
  rw [SupportProof.relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hseedj := InternalGraphCompositionFunctionalityProof.renameInto hseed j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hseedj
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hsj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hmj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at htj
  have hownrankj := InternalGraphCompositionFunctionalityProof.renameInto hownrank j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hownrankj
  exact at2 n (raw.relabel j) (param.relabel j) (index.relabel j) (seed.relabel j) (rank.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j) (value.relabel j) (ownrank.relabel j) root hseedj hbj hsj hfj hmj htj hownrankj hx

theorem at0 (raw param index seed rank depth frontier table value : OTerm alpha)
    (hseed : Nonempty (Derivation body Delta (graph2 OriginalEnumerationRecursionInterface.R rank seed param)))
    (hb : Nonempty (Derivation body Delta (PrimaryUncoveredCount.bounded index rank)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract depth index rank)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationRecursionInterface.D) frontier depth seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationRecursionInterface.R OriginalEnumerationRecursionInterface.D (OriginalEnumerationRecursionInterface.G n)) table (suc index) seed param)))
    : Nonempty (Derivation body Delta (SupportProof.relation n raw param table value)) := by
  apply programCases OriginalEnumerationRecursionInterface.R (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta ownrank hj hx
  rw [SupportProof.relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hseedj := InternalGraphCompositionFunctionalityProof.renameInto hseed j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hseedj
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hsj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at hmj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,PrimaryUncoveredCount.OrderProof.boundedRename] at htj
  exact at1 n (raw.relabel j) (param.relabel j) (index.relabel j) (seed.relabel j) (rank.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j) (value.relabel j) ownrank hseedj hbj hsj hfj hmj htj hx

theorem alignedExtraction : Targets.InternalAlignedExtraction := by
  intro n body alpha Delta raw param index seed rank depth frontier table value hr hb hs hf hm ht
  have h := at0 n raw param index seed rank depth frontier table value hr hb hs hf hm ht
  constructor
  · intro he
    obtain ⟨hi⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
  · intro hl
    obtain ⟨hi⟩ := andRight h
    obtain ⟨hl⟩ := hl
    exact ⟨Derivation.implicationElimination hi hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Extraction.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Extraction.Proof
