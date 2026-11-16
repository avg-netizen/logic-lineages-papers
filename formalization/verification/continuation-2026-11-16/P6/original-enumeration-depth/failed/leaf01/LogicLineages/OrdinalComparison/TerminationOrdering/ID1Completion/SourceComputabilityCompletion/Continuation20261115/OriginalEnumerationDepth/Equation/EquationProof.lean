module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.OwnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.EquationProof
open OriginalDecodedExchangeEquation
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
variable (n : Nat)
attribute [local irreducible] programGraph

def relation (node param values value : OTerm alpha) : Formula alpha :=
  ((graph2 (OriginalEnumerationDepth.extract n) value node param).imp
    (graph3 (OriginalEnumerationDepth.layer n) (suc value) node values param)) ⊓
  ((graph3 (OriginalEnumerationDepth.layer n) (suc value) node values param).imp
    (graph2 (OriginalEnumerationDepth.extract n) value node param))
theorem relationRename {beta : Type} (node param values value : OTerm alpha) (j : alpha → beta) :
    (relation n node param values value).relabel j =
      relation n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) := by
  simp only [relation,conjunctionRename,InternalBetaExtensionSyntaxProof.impRename,graph2Rename,graph3Rename,sucRelabel]

theorem atSome (node param values value rank old deps inner : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.layer n) (suc inner) node values param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  have hv : Nonempty (Derivation body Delta (graph2 (answerMap n) values deps param)) :=
    binaryRecover (answerMap n) OriginalEnumerationDepth.dependency (.projection 1)
      values deps param ![node,param] ha hd (projectionValue 1 ![node,param])
  have hm := MapProof.transport (OriginalEnumerationDepth.extract n) deps param old values
    (OwnProof.agreement n node param rank old deps hr ho hd) hv
  have he := ArgumentEntriesConsTable.FinalProof.finalAnswers body alpha Delta
    OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency
    (OriginalEnumerationDepth.layer n) node param rank old deps values inner hr ho hd hm hg
  apply andIntro
  · let E := graph2 (OriginalEnumerationDepth.extract n) value node param
    have hh : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique (OriginalEnumerationDepth.extract n) inner value ![node,param] (withHyp he E) hh
    obtain ⟨hout⟩ := outputTransport (OriginalEnumerationDepth.layer n) (suc inner) (suc value)
      ![node,values,param] ⟨congSuc hq⟩ (withHyp hg E)
    exact ⟨Derivation.implicationIntroduction hout⟩
  · let G := graph3 (OriginalEnumerationDepth.layer n) (suc value) node values param
    have hh : Nonempty (Derivation body (G :: Delta) G) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hq⟩ := valueUnique (OriginalEnumerationDepth.layer n) (suc inner) (suc value)
      ![node,values,param] (withHyp hg G) hh
    obtain ⟨hout⟩ := outputTransport (OriginalEnumerationDepth.extract n) inner value ![node,param] ⟨cancelSuc hq⟩ (withHyp he G)
    exact ⟨Derivation.implicationIntroduction hout⟩

theorem atOutput (node param values value rank old deps output : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    (hg : Nonempty (Derivation body Delta (graph3 (OriginalEnumerationDepth.layer n) output node values param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  have hn : Nonempty (Derivation body Delta (eqn output z).not) :=
    OriginalEnumerationDepth.LayerProof.layerNonzero n body alpha Delta node values param output hg
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
    have hs := outputTransport (OriginalEnumerationDepth.layer n) (output.relabel j) (suc inner)
      ![node.relabel j,values.relabel j,param.relabel j] he hgj
    exact atSome n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) inner hrj hoj hdj haj hs

theorem atDependencies (node param values value rank old deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) old rank node param)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.dependency deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  apply programCases (OriginalEnumerationDepth.layer n) (Fin.cons node (Fin.cons values (Fin.cons param Fin.elim0))) _
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
  exact atOutput n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) (deps.relabel j) output hrj hoj hdj haj hx

theorem atOld (node param values value rank old : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank node param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) old rank node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  apply programCases OriginalEnumerationDepth.dependency (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hoj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atDependencies n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) (old.relabel j) deps hrj hoj hx haj

theorem atRank (node param values value rank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalEnumerationDepth.rank rank node param)))
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalEnumerationDepth.rank OriginalEnumerationDepth.dependency (OriginalEnumerationDepth.layer n)) (Fin.cons rank (Fin.cons node (Fin.cons param Fin.elim0))) _
  intro beta j Theta old hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atOld n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) (rank.relabel j) old hrj hx haj

theorem equation (node param values value : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 (answers n) values node param)))
    : Nonempty (Derivation body Delta (relation n node param values value)) := by
  apply programCases OriginalEnumerationDepth.rank (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta rank hj hx
  simp only [consTermRename,emptyRename,sucRelabel,zRelabel] at hx
  rw [relationRename]
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at haj
  exact atRank n (node.relabel j) (param.relabel j) (values.relabel j) (value.relabel j) rank hx haj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.EquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.Equation.EquationProof
