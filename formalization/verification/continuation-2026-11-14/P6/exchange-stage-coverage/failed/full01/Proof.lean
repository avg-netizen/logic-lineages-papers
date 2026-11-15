module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
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
theorem step (D : Program 2) (G : Program 3) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw D G raw))) :
    Nonempty (Derivation body Delta (AtRaw D G raw)) := by
  apply atRawIntro D G raw
  let A : Formula (alpha ⊕ Fin 7) := fields D G (raw.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))
  let j : alpha → alpha ⊕ Fin 7 := Sum.inl
  let Theta : List (Formula (alpha ⊕ Fin 7)) := Delta.map (fun q => q.relabel j)
  have hi : ∀ q ∈ Delta, q.relabel j ∈ Theta := by
    intro q hq
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have hbj := renameInto hb j Theta hi
  rw [belowRawRename] at hbj
  have hf : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hm := andLeft hf
  have hd := andLeft (andRight hf)
  have ha := andLeft (andRight (andRight hf))
  have hg := andLeft (andRight (andRight (andRight hf)))
  have ho := andRight (andRight (andRight (andRight hf)))
  obtain ⟨h⟩ := CoreProof.core D G (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))
    (withHyp hbj A) hm hd ha hg ho
  exact ⟨Derivation.implicationIntroduction h⟩
theorem coverage : Targets.InternalCoverage := by
  intro body alpha Delta D G raw query old param deps answers value out hm hd ha hg ho
  exact atRawApply D G raw query old param deps answers value out
    (rawInduction D G raw (fun _ _ r h => step D G r h))
    (andIntro hm (andIntro hd (andIntro ha (andIntro hg ho))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
