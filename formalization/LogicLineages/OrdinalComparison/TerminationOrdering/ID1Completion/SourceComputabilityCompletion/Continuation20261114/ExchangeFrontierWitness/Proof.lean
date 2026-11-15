module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
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

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InductionDefinitions InductionSyntaxProof InductionBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem step (D : Program 2) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D raw))) :
    Nonempty (Derivation body Delta (AtRaw D raw)) := by
  apply atRawIntro D raw
  let A : Formula (alpha ⊕ Fin 3) := fields D (raw.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let Theta : List (Formula (alpha ⊕ Fin 3)) := Delta.map (fun q => q.relabel j)
  have hi : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hbj := renameInto hb j Theta hi
  rw [belowRawRename] at hbj
  have hf : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := CoreProof.core D (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (withHyp hbj A) (andLeft hf) (andRight hf)
  exact ⟨Derivation.implicationIntroduction h⟩
theorem flattenWitness : Targets.InternalFlattenWitness := by
  intro body alpha Delta D raw param out child hf hm
  exact atRawApply D raw param out child (rawInduction D raw (fun _ _ r h => step D r h)) (andIntro hf hm)
theorem successorWitness : Targets.InternalSuccessorWitness := by
  intro body alpha Delta D depth seed param frontier out child hf ho hm
  have hflat := (ExchangeFrontier.InternalProof.internalBindSuccessor body alpha Delta D depth seed param frontier out hf).mp ho
  exact flattenWitness body alpha Delta D frontier param out child hflat hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierWitness.Proof
