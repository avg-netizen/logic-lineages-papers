module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.LayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Lists ListSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalHeadDecoderValidity.BackwardProof (orCases)
theorem empty (n : Nat) : Nonempty (Derivation body Delta (AllValid n (z : OTerm alpha))) := by
  apply ListBindingProof.introduce n z
  unfold Lists.matrix
  rw [InternalTagArithmeticSyntaxProof.zRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  exact Derivation.explosion (Classical.choice (OriginalAscendingRange.SupportProof.nilImpossible (.var (Sum.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1))
    (show Nonempty (Derivation body _ (graph2 contains (numeral 1) z (.var (Sum.inr (0 : Fin 1)) : OTerm (alpha ⊕ Fin 1)))) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)))

theorem layer (n : Nat) (xs : Fin 7 → OTerm alpha) (out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (AllValid n (xs 5))))
    (ho : Nonempty (Derivation body Delta (AllValid n (xs 6))))
    (hg : Nonempty (Derivation body Delta (programGraph (OriginalEnumerationConstructorLayer.layer n) out xs))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply ListBindingProof.introduce n out
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  let M : Formula (alpha ⊕ Fin 1) := graph2 contains (numeral 1) (out.relabel Sum.inl) (.var (.inr 0))
  let Theta := M :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1))
  have hj : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hpj := renameInto hp (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  have hoj := renameInto ho (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [allRename] at hpj hoj
  have hgj := renameInto hg (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [programRename] at hgj
  exact Classical.choice (LayerProof.member n (fun i => (xs i).relabel Sum.inl) (out.relabel Sum.inl) (.var (.inr 0))
    hpj hoj hgj ⟨Derivation.hypothesis List.mem_cons_self⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListClosureProof
