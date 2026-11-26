module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphCompositionFunctionalityProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem capacity : Targets.InternalCapacity := by
  intro n body alpha Delta index previous seed param frontier node seedRank nodeRank hr hb hf hm hc
  apply programCases InternalEqualityTest.subtract (Fin.cons index (Fin.cons seedRank Fin.elim0)) _
  intro beta j Theta depth hj hs
  simp only [consTermRename,emptyRename] at hs
  simp only [PrimaryUncoveredCount.OrderProof.boundedRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [PrimaryUncoveredCount.OrderProof.boundedRename] at hbj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [InternalControlGraphSupportProof.programRename] at hfj
  have hfxs : (fun i => (![index,previous,seed,param] i).relabel j) = ![index.relabel j,previous.relabel j,seed.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hfxs] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename] at hcj
  have hfront := SupportProof.frontierRecover (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)
    (index.relabel j) (previous.relabel j) (seed.relabel j) (param.relabel j) (seedRank.relabel j) depth (frontier.relabel j) hrj hs hfj
  exact SupportProof.capacityAt n (index.relabel j) (seed.relabel j) (param.relabel j) depth (frontier.relabel j)
    (node.relabel j) (seedRank.relabel j) (nodeRank.relabel j) hrj hbj hs hfront hmj hcj

theorem previousFrontier : Targets.InternalPreviousFrontier := by
  intro n body alpha Delta index previous older seed param current prior node deps child seedRank hr hb hf hp hm hd hc
  apply programCases InternalEqualityTest.subtract (Fin.cons (suc index) (Fin.cons seedRank Fin.elim0)) _
  intro beta j Theta depth hj hs
  simp only [consTermRename,emptyRename,sucRelabel] at hs
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename] at hrj
  have hbj := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [PrimaryUncoveredCount.OrderProof.boundedRename,sucRelabel] at hbj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [InternalControlGraphSupportProof.programRename] at hfj
  have hfxs : (fun i => (![suc index,previous,seed,param] i).relabel j) = ![suc (index.relabel j),previous.relabel j,seed.relabel j,param.relabel j] := by
    funext i
    fin_cases i
    · change (suc index).relabel j = suc (index.relabel j)
      exact sucRelabel index j
    · rfl
    · rfl
    · rfl
  rw [hfxs] at hfj
  have hpj := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [InternalControlGraphSupportProof.programRename] at hpj
  have hpxs : (fun i => (![index,older,seed,param] i).relabel j) = ![index.relabel j,older.relabel j,seed.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hpxs] at hpj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename] at hdj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have ha := SubtractionAlignment.Proof.predecessorAlignment body beta Theta (index.relabel j) (seedRank.relabel j) depth hbj hs
  have hcurrent := SupportProof.frontierRecover (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)
    (suc (index.relabel j)) (previous.relabel j) (seed.relabel j) (param.relabel j) (seedRank.relabel j) depth (current.relabel j) hrj hs hfj
  have hprior := SupportProof.frontierRecover (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)
    (index.relabel j) (older.relabel j) (seed.relabel j) (param.relabel j) (seedRank.relabel j) (suc depth) (prior.relabel j) hrj ha hpj
  exact ExchangeFrontierCoverage.Proof.successorCoverage body beta Theta (OriginalDecodedDependencies.dependencies n)
    depth (seed.relabel j) (param.relabel j) (current.relabel j) (node.relabel j)
    (deps.relabel j) (child.relabel j) (prior.relabel j) hcurrent hmj hdj hcj hprior

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierCapacity.Proof
