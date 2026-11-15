module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.ValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.AgreementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.ZeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BridgeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 SideProof FrameProof
open OriginalMapGraphTransport.Targets OriginalMapGraphTransport.AgreementSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat} {arity : Fin n → Nat} {V : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3}
attribute [local irreducible] programGraph
theorem fromAgreement {raw param : OTerm alpha} (s1 s2 : Side n arity V body Delta raw param)
    (old1 old2 deps found : OTerm alpha)
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) old2 s2.index s2.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement deps old1 old2)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old1 Fin.elim0)) _
  intro beta j Theta answers hj hv
  simp only [consTermRename,emptyRename] at hv
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  rw [graph3Rename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  rw [graph3Rename] at h2j
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  rw [agreementRename] at haj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  have hv2 := OriginalMapGraphTransport.Proof.transport body beta Theta (deps.relabel j) (old1.relabel j) (old2.relabel j) answers haj hv
  exact ValuesProof.sharedAnswers t1 t2 (old1.relabel j) (old2.relabel j) (deps.relabel j) answers (found.relabel j) h1j h2j hdj hv hv2 hlj

theorem emptyMap (deps old : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn deps z))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph z deps old)) := by
  have h0 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph z z old)) :=
    InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) ExchangeMapGraph.mapStep z (Fin.cons old Fin.elim0)
      (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons old Fin.elim0))
  obtain ⟨hz⟩ := hz
  exact headTransport ExchangeMapGraph.mapGraph z z deps (Fin.cons old Fin.elim0) ⟨symm hz⟩ h0

theorem fromEmpty {raw param : OTerm alpha} (s1 s2 : Side n arity V body Delta raw param)
    (old1 old2 deps found : OTerm alpha)
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) old2 s2.index s2.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (hz : Nonempty (Derivation body Delta (eqn deps z))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) :=
  ValuesProof.sharedAnswers s1 s2 old1 old2 deps z found h1 h2 hd (emptyMap deps old1 hz) (emptyMap deps old2 hz) hl

theorem atFrame {raw param : OTerm alpha} (f : Frame n arity V body Delta raw param)
    (budget deps found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n arity V budget)))
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.s1.table raw))) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found f.s2.table raw)) :=
  fromAgreement f.s1 f.s2 f.old1 f.old2 deps found f.oldGraph1 f.oldGraph2 hd
    (AgreementProof.agreement f budget deps ih hr hd) hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BridgeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.BridgeProof
