module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsProof
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
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem step (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let A : Formula (alpha ⊕ Fin 2) := graph2 contains (.var (.inr 1)) (raw.relabel Sum.inl) (.var (.inr 0))
  let j : alpha → alpha ⊕ Fin 2 := Sum.inl
  let Theta : List (Formula (alpha ⊕ Fin 2)) := Delta.map (fun q => q.relabel j)
  have hi : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hbj := renameInto hb j Theta hi
  rw [belowRawRename] at hbj
  obtain ⟨h⟩ := ContainsCoreProof.core (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (withHyp hbj A) (show Nonempty (Derivation body (A :: Delta.map (fun q => q.relabel Sum.inl)) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem containsRange : Targets.InternalContainsRange := by
  intro body alpha Delta raw needle out hm
  exact atRawApply raw needle out (rawInduction raw (fun _ _ r h => step r h)) hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsProof
