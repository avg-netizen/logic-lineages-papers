module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.BridgeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.CasesProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel eqnRelabel zRelabel)
open InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 SideProof FrameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable {n : Nat}
attribute [local irreducible] programGraph
def weakenSide {raw param : OTerm alpha} (s : Side n body Delta raw param) (A : Formula alpha) :
    Side n body (A :: Delta) raw param where
  index := s.index
  seed := s.seed
  seedRank := s.seedRank
  depth := s.depth
  frontier := s.frontier
  table := s.table
  rankGraph := withHyp s.rankGraph A
  bounded := withHyp s.bounded A
  subtraction := withHyp s.subtraction A
  front := withHyp s.front A
  member := withHyp s.member A
  tableGraph := withHyp s.tableGraph A

theorem atNexts {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 old2 pred1 pred2 next1 next2 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param)))
    (hi1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn s2.index (suc pred2))))
    (hf1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next1 (suc s1.depth) s1.seed param)))
    (hf2 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next2 (suc s2.depth) s2.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  let f : Frame n body Delta raw param := {
    s1 := s1, s2 := s2, old1 := old1, old2 := old2, pred1 := pred1, pred2 := pred2,
    next1 := next1, next2 := next2, index1 := hi1, index2 := hi2,
    oldGraph1 := h1, oldGraph2 := h2, nextGraph1 := hf1, nextGraph2 := hf2 }
  exact BridgeProof.atFrame f budget deps found ih hr hd hl

theorem atNext1 {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 old2 pred1 pred2 next1 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param)))
    (hi1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn s2.index (suc pred2))))
    (hf1 : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) next1 (suc s1.depth) s1.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) (Fin.cons (suc s2.depth) (Fin.cons (s2.seed) (Fin.cons (param) (Fin.elim0)))) _
  intro beta j Theta next2 hj hx
  simp only [consTermRename,emptyRename,sucRelabel] at hx
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename] at hdj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename] at hlj
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph3Rename,sucRelabel] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph3Rename,sucRelabel] at h2j
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [eqnRelabel,sucRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [eqnRelabel,sucRelabel] at hi2j
  have hf1j := InternalGraphCompositionFunctionalityProof.renameInto hf1 j Theta hj
  simp only [graph3Rename,sucRelabel] at hf1j
  exact atNexts t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) (old1.relabel j) (old2.relabel j) (pred1.relabel j) (pred2.relabel j) (next1.relabel j) next2 ihj hrj hdj hlj h1j h2j hi1j hi2j hf1j hx

theorem atSuccessors {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 old2 pred1 pred2 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param)))
    (hi1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1))))
    (hi2 : Nonempty (Derivation body Delta (eqn s2.index (suc pred2))))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases (ExchangeFrontier.bindList OriginalEnumerationFields.dependency) (Fin.cons (suc s1.depth) (Fin.cons (s1.seed) (Fin.cons (param) (Fin.elim0)))) _
  intro beta j Theta next1 hj hx
  simp only [consTermRename,emptyRename,sucRelabel] at hx
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename] at hdj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename] at hlj
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph3Rename,sucRelabel] at h1j
  have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
  simp only [graph3Rename,sucRelabel] at h2j
  have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
  simp only [eqnRelabel,sucRelabel] at hi1j
  have hi2j := InternalGraphCompositionFunctionalityProof.renameInto hi2 j Theta hj
  simp only [eqnRelabel,sucRelabel] at hi2j
  exact atNext1 t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) (old1.relabel j) (old2.relabel j) (pred1.relabel j) (pred2.relabel j) next1 ihj hrj hdj hlj h1j h2j hi1j hi2j hx

theorem atIndex1 {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 old2 pred1 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param)))
    (hi1 : Nonempty (Derivation body Delta (eqn s1.index (suc pred1))))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply zeroSuccessorCases Delta s2.index _
  · let A := eqn s2.index z
    let t1 := weakenSide s1 A
    let t2 := weakenSide s2 A
    have hz := ZeroProof.dependencyZero t2 budget deps (withHyp hr A) (withHyp hd A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BridgeProof.fromEmpty t1 t2 old1 old2 deps found (withHyp h1 A) (withHyp h2 A) (withHyp hd A) (withHyp hl A) hz
  · intro beta j Theta pred2 hj hx
    rw [graph2Rename]
    let t1 := s1.rename j Theta hj
    let t2 := s2.rename j Theta hj
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [InductionSyntaxProof.belowRawRename] at ihj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    simp only [graph2Rename] at hrj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename] at hdj
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    simp only [graph2Rename] at hlj
    have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
    simp only [graph3Rename,sucRelabel] at h1j
    have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
    simp only [graph3Rename,sucRelabel] at h2j
    have hi1j := InternalGraphCompositionFunctionalityProof.renameInto hi1 j Theta hj
    simp only [eqnRelabel,sucRelabel] at hi1j
    exact atSuccessors t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) (old1.relabel j) (old2.relabel j) (pred1.relabel j) pred2 ihj hrj hdj hlj h1j h2j hi1j hx

theorem atOlds {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 old2 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    (h2 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old2 s2.index s2.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply zeroSuccessorCases Delta s1.index _
  · let A := eqn s1.index z
    let t1 := weakenSide s1 A
    let t2 := weakenSide s2 A
    have hz := ZeroProof.dependencyZero t1 budget deps (withHyp hr A) (withHyp hd A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BridgeProof.fromEmpty t1 t2 old1 old2 deps found (withHyp h1 A) (withHyp h2 A) (withHyp hd A) (withHyp hl A) hz
  · intro beta j Theta pred1 hj hx
    rw [graph2Rename]
    let t1 := s1.rename j Theta hj
    let t2 := s2.rename j Theta hj
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    simp only [InductionSyntaxProof.belowRawRename] at ihj
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    simp only [graph2Rename] at hrj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename] at hdj
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    simp only [graph2Rename] at hlj
    have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
    simp only [graph3Rename,sucRelabel] at h1j
    have h2j := InternalGraphCompositionFunctionalityProof.renameInto h2 j Theta hj
    simp only [graph3Rename,sucRelabel] at h2j
    exact atIndex1 t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) (old1.relabel j) (old2.relabel j) pred1 ihj hrj hdj hlj h1j h2j hx

theorem atOld1 {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found old1 : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    (h1 : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) old1 s1.index s1.seed param)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) (Fin.cons (s2.index) (Fin.cons (s2.seed) (Fin.cons (param) (Fin.elim0)))) _
  intro beta j Theta old2 hj hx
  simp only [consTermRename,emptyRename] at hx
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename] at hdj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename] at hlj
  have h1j := InternalGraphCompositionFunctionalityProof.renameInto h1 j Theta hj
  simp only [graph3Rename,sucRelabel] at h1j
  exact atOlds t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) (old1.relabel j) old2 ihj hrj hdj hlj h1j hx

theorem atDeps {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget deps found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalEnumerationFields.rank OriginalEnumerationFields.dependency (OriginalEnumerationFields.layer n)) (Fin.cons (s1.index) (Fin.cons (s1.seed) (Fin.cons (param) (Fin.elim0)))) _
  intro beta j Theta old1 hj hx
  simp only [consTermRename,emptyRename] at hx
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename] at hdj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename] at hlj
  exact atOld1 t1 t2 (budget.relabel j) (deps.relabel j) (found.relabel j) old1 ihj hrj hdj hlj hx

theorem core {raw param : OTerm alpha} (s1 s2 : Side n body Delta raw param)
    (budget found : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (InductionDefinitions.BelowRaw n budget)))
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank budget raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s1.table raw)))
    : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found s2.table raw)) := by
  apply programCases OriginalEnumerationFields.dependency (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hd
  simp only [consTermRename,emptyRename] at hd
  rw [graph2Rename]
  let t1 := s1.rename j Theta hj
  let t2 := s2.rename j Theta hj
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  simp only [InductionSyntaxProof.belowRawRename] at ihj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename] at hlj
  exact atDeps t1 t2 (budget.relabel j) deps (found.relabel j) ihj hrj hd hlj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.CasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.CacheCoherence.CasesProof
