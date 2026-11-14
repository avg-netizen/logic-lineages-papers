module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.AllCountsProof
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

open InductionDefinitions InductionSyntaxProof InductionBindingProof

theorem step (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let Theta : List (Formula (alpha ⊕ Fin 1)) := Delta.map (fun q => q.relabel j)
  have hi : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hbj := renameInto hb j Theta hi
  rw [belowRawRename] at hbj
  exact CoreProof.core (raw.relabel j) (.var (.inr 0)) hbj

theorem allCounts : Targets.InternalAllCounts := by
  intro body alpha Delta candidates list
  exact atRawApply candidates list (rawInduction candidates (fun _ _ r h => step r h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.AllCountsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentPermutationReflexivity.AllCountsProof
