module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.AllCountsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformVertexPathSupportProof

theorem permutation : Targets.InternalPermutation := by
  intro body alpha Delta list
  apply programCases InternalApplicationValidityStackAppend.append (Fin.cons list (Fin.cons list Fin.elim0)) _
  intro beta j Theta candidates hj hc
  simp only [consTermRename,emptyRename] at hc
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  let xs : Fin 2 → OTerm beta := Fin.cons (list.relabel j) (Fin.cons (list.relabel j) Fin.elim0)
  exact ternaryValue ArgumentCountComparison.allCounts InternalApplicationValidityStackAppend.append
    (.projection 0) (.projection 1) (numeral 1) candidates (list.relabel j) (list.relabel j) xs
    (AllCountsProof.allCounts body beta Theta candidates (list.relabel j)) hc
    (projectionValue 0 xs) (projectionValue 1 xs)

theorem original : Targets.InternalOriginal := by
  intro body alpha Delta base list he
  exact (OriginalArgumentPermutation.InternalProof.internalSome body alpha Delta base base list list (numeral 1) he he).mpr
    (permutation body alpha Delta list)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.Proof
