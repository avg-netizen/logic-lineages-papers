module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.OwnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.EquationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph

def relation (node param values value : OTerm alpha) : Formula alpha :=
  ((graph2 (exchange n arity) value node param).imp
    (graph3 (OriginalDecodedLayerCalibration.layer n arity) (suc value) node values param)) ⊓
  ((graph3 (OriginalDecodedLayerCalibration.layer n arity) (suc value) node values param).imp
    (graph2 (exchange n arity) value node param))
theorem relationRename {beta : Type} (node param values value : OTerm alpha) (j : alpha → beta) :
    (relation n arity node param values value).relabel j =
      relation n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) := by
  simp only [relation,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,graph2Rename,graph3Rename,sucRelabel]

theorem atSome (node param values value rank old deps inner : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (suc inner) node values param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  have hv : Nonempty (Derivation body Delta (graph2 (answerMap n arity) values deps param)) :=
    binaryRecover (answerMap n arity) (OriginalDecodedDependencies.dependencies n) (.projection 1)
      values deps param ![node,param] ha hd (projectionValue 1 ![node,param])
  have hm := MapProof.transport (exchange n arity) deps param old values
    (OwnProof.agreement n arity node param rank old deps hr ho hd) hv
  have he := ArgumentEntriesConsTable.FinalProof.finalAnswers body alpha Delta
    (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n)
    (OriginalDecodedLayerCalibration.layer n arity) node param rank old deps values inner hr ho hd hm hg
  apply andIntro
  · let E := graph2 (exchange n arity) value node param
    have hh : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique (exchange n arity) inner value ![node,param] (withHyp he E) hh
    obtain ⟨hout⟩ := outputTransport (OriginalDecodedLayerCalibration.layer n arity) (suc inner) (suc value)
      ![node,values,param] ⟨congSuc hq⟩ (withHyp hg E)
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let G := graph3 (OriginalDecodedLayerCalibration.layer n arity) (suc value) node values param
    have hh : Nonempty (Derivation body (G :: Delta) G) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique (OriginalDecodedLayerCalibration.layer n arity) (suc inner) (suc value)
      ![node,values,param] (withHyp hg G) hh
    obtain ⟨hout⟩ := outputTransport (exchange n arity) inner value ![node,param] ⟨cancelSuc hq⟩ (withHyp he G)
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem atOutput (node param values value rank old deps output : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) output node values param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  have hn : Nonempty (Derivation body Delta (eqn output z).not) :=
    OriginalDecodedCacheDomain.LayerProof.optionalNonzero _ (OriginalDecodedLayerCalibration.guard n) node values param output hg
  apply zeroSuccessorCases Delta output _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta inner hj he
    rw [relationRename]
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
    have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdj
    have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
    have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hgj
    have hs := outputTransport (OriginalDecodedLayerCalibration.layer n arity) (output.relabel j) (suc inner)
      ![node.relabel j,values.relabel j,param.relabel j] he hgj
    exact atSome n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) inner hrj hoj hdj haj hs

theorem atDependencies (node param values value rank old deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  apply programCases (OriginalDecodedLayerCalibration.layer n arity) (Fin.cons node (Fin.cons values (Fin.cons param Fin.elim0))) _
  intro beta j Theta output hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atOutput n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) output hrj hoj hdj haj hx

theorem atOld (node param values value rank old : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)) old rank node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  apply programCases (OriginalDecodedDependencies.dependencies n) (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atDependencies n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) deps hrj hoj hx haj

theorem atRank (node param values value rank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) rank node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  apply programCases (ExchangeGraphRecursion.graph (OriginalDecodedRank.rank n) (OriginalDecodedDependencies.dependencies n) (OriginalDecodedLayerCalibration.layer n arity)) (Fin.cons rank (Fin.cons node (Fin.cons param Fin.elim0))) _
  intro beta j Theta old hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atOld n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) old hrj hx haj

theorem equation (node param values value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (answers n arity) values node param)))
    : Nonempty (Derivation body Delta (relation n arity node param values value)) := by
  apply programCases (OriginalDecodedRank.rank n) (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta rank hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atRank n arity (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) rank hx haj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.EquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.EquationProof
