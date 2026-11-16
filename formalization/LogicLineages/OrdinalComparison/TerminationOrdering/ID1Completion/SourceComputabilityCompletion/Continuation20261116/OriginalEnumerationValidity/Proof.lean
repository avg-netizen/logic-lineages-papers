module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.RankStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261115 Lists ListSyntaxProof InductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem enumerationValid (n : Nat) (node param out : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply programCases OriginalEnumerationRecursionInterface.R (Fin.cons node (Fin.cons param Fin.elim0)) _
  intro beta j Theta fuel hj hr
  rw [allRename]
  simp only [consTermRename,emptyRename] at hr
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hej
  exact atRankApply n fuel (node.relabel j) (param.relabel j) (out.relabel j)
    (rankInduction n fuel (fun _ _ r ih => RankStepProof.step n r ih)) (andIntro hr hej)

theorem internalEnumerationValidity : Targets.InternalEnumerationValidity := by
  intro n body alpha Delta node param out raw he hm
  exact ListBindingProof.member n out raw (enumerationValid n node param out he) hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.Proof
