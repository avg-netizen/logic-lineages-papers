module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.SideProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.ValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 SideProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
theorem atSome {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (old1 old2 deps answers value found : OTerm alpha)
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old2 s2.index s2.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old2)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (hv : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) (suc value) raw answers param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  have hc1 := ExchangeStageCoverage.Proof.coverage body alpha Delta OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)
    s1.frontier raw old1 param deps answers value s1.table s1.member hd ha1 hv (sideStage s1 old1 h1)
  have hc2 := ExchangeStageCoverage.Proof.coverage body alpha Delta OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)
    s2.frontier raw old2 param deps answers value s2.table s2.member hd ha2 hv (sideStage s2 old2 h2)
  obtain ⟨he⟩ := valueUnique ExchangeMapGraph.lookup found (suc value) ![s1.table,raw] hl hc1
  exact outputTransport ExchangeMapGraph.lookup (suc value) found ![s2.table,raw] ⟨symm he⟩ hc2

theorem atValue {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (old1 old2 deps answers value found : OTerm alpha)
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old2 s2.index s2.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old2)))
    (hv : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) value raw answers param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  have hn : Nonempty (Derivation body Delta (eqn value z).not) :=
    OriginalCodeBoundsRecursion.NonzeroProof.internalLayerNonzero n body alpha Delta raw answers param value hv
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta inner hj he
    rw [graph2Rename]
    let t1 := s1.rename j Theta hj
    let t2 := s2.rename j Theta hj
    have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
    simp only [graph2Rename,graph3Rename] at h1j
    have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
    simp only [graph2Rename,graph3Rename] at h2j
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename,graph3Rename] at hdj
    have ha1j := InternalGraphCompositionFunctionalityProof.renameInto ha1 j Theta hj
    simp only [graph2Rename,graph3Rename] at ha1j
    have ha2j := InternalGraphCompositionFunctionalityProof.renameInto ha2 j Theta hj
    simp only [graph2Rename,graph3Rename] at ha2j
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph2Rename,graph3Rename] at hvj
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    simp only [graph2Rename,graph3Rename] at hlj
    have hs := outputTransport (OriginalCodeBoundsRecursion.layer n) (value.relabel j) (suc inner) ![raw.relabel j,answers.relabel j,param.relabel j] he hvj
    exact atSome t1 t2 (old1.relabel j) (old2.relabel j) (deps.relabel j) (answers.relabel j) inner (found.relabel j) h1j h2j hdj ha1j ha2j hlj hs

theorem sharedAnswers {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (old1 old2 deps answers found : OTerm alpha)
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old2 s2.index s2.seed param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (ha1 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old1)))
    (ha2 : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old2)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases (OriginalCodeBoundsRecursion.layer n) (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta value hj hv
  simp only [consTermRename,emptyRename] at hv
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph2Rename,graph3Rename] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph2Rename,graph3Rename] at h2j
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename] at hdj
  have ha1j := InternalGraphCompositionFunctionalityProof.renameInto ha1 j Theta hj
  simp only [graph2Rename,graph3Rename] at ha1j
  have ha2j := InternalGraphCompositionFunctionalityProof.renameInto ha2 j Theta hj
  simp only [graph2Rename,graph3Rename] at ha2j
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename] at hlj
  exact atValue t1 t2 (old1.relabel j) (old2.relabel j) (deps.relabel j) (answers.relabel j) value (found.relabel j) h1j h2j hdj ha1j ha2j hv hlj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.ValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.ValuesProof
