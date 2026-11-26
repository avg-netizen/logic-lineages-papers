module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.DependencyCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalRecursionClosureLogicProof (closedApply)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114.ArgumentEntriesDependencyDescent.SupportProof (strictRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem descent (key param deps child parentRank childRank : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 rank parentRank key param)))
    (hd : Nonempty (Derivation body Delta (graph2 dependency deps key param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) deps child)))
    (hr : Nonempty (Derivation body Delta (graph2 rank childRank child param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank)) := by
  have hl := unaryRecover InternalUnpair.left (.projection 0) parentRank key ![key,param]
    hp (projectionValue 0 ![key,param])
  apply programCases InternalUnpair.right (Fin.cons key Fin.elim0) _
  intro beta j Theta bound hj hbound
  simp only [consTermRename,emptyRename] at hbound
  rw [strictRename]
  have hlj := renameInto hl j Theta hj
  rw [graph1Rename] at hlj
  have hpair := closedApply
    (InternalUnpairReverseProof.actualOriginalUnpairReverseInverse body beta (key.relabel j) (parentRank.relabel j) bound)
    (andIntro hlj hbound)
  have hdj := renameInto hd j Theta hj
  have hmj := renameInto hm j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hdj hmj hrj
  exact DependencyCasesProof.pairedDescent (key.relabel j) (parentRank.relabel j) bound
    (param.relabel j) (deps.relabel j) (child.relabel j) (childRank.relabel j) hpair hdj hmj hrj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.RankDescentProof
