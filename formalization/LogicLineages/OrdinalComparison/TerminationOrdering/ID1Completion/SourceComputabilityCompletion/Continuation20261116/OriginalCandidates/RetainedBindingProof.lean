module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (emb eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RetainedSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduce (H : Program 1) (seed param candidate gamma value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.gamma gamma seed param)))
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value candidate gamma)))
    (hn : Nonempty (Derivation body Delta (eqn value (numeral 0)).not)) :
    Nonempty (Derivation body Delta (Targets.retained H seed param candidate)) := by
  rw [frozenBlock]
  apply InternalFiniteBlocksProof.introduction body alpha 2 Delta _ (fun i => emb ((![gamma,value] : Fin 2 → OTerm alpha) i))
  rw [matrixWitness]
  exact andIntro (andIntro hg hv) hn

theorem cases (H : Program 1) (seed param candidate : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (Targets.retained H seed param candidate)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (gamma value : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 OriginalClassCodes.gamma gamma (seed.relabel j) (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (OriginalTypedDecoder.packedCheck H) value (candidate.relabel j) gamma)) →
      Nonempty (Derivation body Theta (eqn value (numeral 0)).not) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  rw [frozenBlock] at h
  apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (matrix H seed param candidate) psi h
  let Theta := matrix H seed param candidate :: Delta.map (fun q => q.relabel Sum.inl)
  have hm : Nonempty (Derivation body Theta (matrix H seed param candidate)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact next (alpha ⊕ Fin 2) Sum.inl Theta (.var (.inr 0)) (.var (.inr 1))
    (by intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    (andLeft (andLeft hm)) (andRight (andLeft hm)) (andRight hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.RetainedBindingProof
