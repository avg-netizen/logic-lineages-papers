module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectIntroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open EraseInvariant Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem introduce (raw needle rest bit : OTerm alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (query lc rc : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntryCount.count lc (raw.relabel j) query)) →
      Nonempty (Derivation body Theta (graph2 ArgumentEntryCount.count rc (rest.relabel j) query)) →
      Nonempty (Derivation body Theta
        (((eqn (needle.relabel j) query).imp (eqn lc (OrdinaryArithmetic.addTerm rc (bit.relabel j)))) ⊓
         ((eqn (needle.relabel j) query).not.imp (eqn lc rc))))) :
    Nonempty (Derivation body Delta (countEffect raw needle rest bit)) := by
  unfold countEffect
  apply InternalClosedProgramsBindingProof.introduction body alpha 3 Delta
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let f := graph2 ArgumentEntryCount.count (x 1) (raw.relabel Sum.inl) (x 0) ⊓
    graph2 ArgumentEntryCount.count (x 2) (rest.relabel Sum.inl) (x 0)
  let Theta : List (Formula (alpha ⊕ Fin 3)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  obtain ⟨d⟩ := next (alpha ⊕ Fin 3) Sum.inl Theta (x 0) (x 1) (x 2) hi (andLeft hf) (andRight hf)
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectIntroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountEffectIntroProof
