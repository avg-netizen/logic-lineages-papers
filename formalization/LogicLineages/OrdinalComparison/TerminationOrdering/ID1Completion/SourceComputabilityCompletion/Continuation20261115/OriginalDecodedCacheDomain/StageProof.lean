module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.StageProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atValue (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (frontier old param table node found deps answers value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hv : Nonempty (Derivation body Delta (graph3 (ConcreteHeadMoveLayer.layer n arity V) value node answers param)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  have hn : Nonempty (Derivation body Delta (eqn value z).not) :=
    LayerProof.optionalNonzero _ V node answers param value hv
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta inner hj he
    simp only [eqnRelabel,zRelabel]
    have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
    have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
    have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
    have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at haj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
    have hs := outputTransport (ConcreteHeadMoveLayer.layer n arity V) (value.relabel j) (suc inner)
      ![node.relabel j,answers.relabel j,param.relabel j] he hvj
    have hc := ExchangeStageCoverage.Proof.coverage body beta Theta (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)
      (frontier.relabel j) (node.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) inner (table.relabel j)
      hmj hdj haj hs htj
    exact LayerProof.unequalZero (found.relabel j) inner (valueUnique ExchangeMapGraph.lookup (found.relabel j) (suc inner)
      ![table.relabel j,node.relabel j] hlj hc)

theorem atAnswers (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (frontier old param table node found deps answers : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases (ConcreteHeadMoveLayer.layer n arity V) (Fin.cons node (Fin.cons answers (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta value hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [eqnRelabel,zRelabel]
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at haj
  exact atValue n arity V (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) (deps.relabel j) (answers.relabel j) value htj hmj hlj hdj haj hx

theorem atDeps (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (frontier old param table node found deps : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old (Fin.elim0))) _
  intro beta j Theta answers hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [eqnRelabel,zRelabel]
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdj
  exact atAnswers n arity V (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) (deps.relabel j) answers htj hmj hlj hdj hx

theorem stageAt (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (frontier old param table node found : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage (OriginalDecodedDependencies.dependencies n) (ConcreteHeadMoveLayer.layer n arity V)) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases (OriginalDecodedDependencies.dependencies n) (Fin.cons node (Fin.cons param (Fin.elim0))) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename] at hx
  simp only [eqnRelabel,zRelabel]
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact atDeps n arity V (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) deps htj hmj hlj hx

theorem stageDomain : Targets.InternalStageDomain := stageAt

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.StageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheDomain.StageProof
