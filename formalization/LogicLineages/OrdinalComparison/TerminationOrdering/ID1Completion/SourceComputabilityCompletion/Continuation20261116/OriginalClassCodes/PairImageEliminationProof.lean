module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PairImageProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem cases (raw param node : OTerm alpha) (psi : Formula alpha)
    (hi : Nonempty (Derivation body Delta (image raw param node)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (source : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 contains (numeral 1) (raw.relabel j) source)) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (node.relabel j) (param.relabel j) source)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨hi⟩ := hi
  apply Nonempty.intro
  apply Derivation.existentialElimination hi
  let Theta : List (Formula (alpha ⊕ Fin 1)) := imageMatrix raw param node :: Delta.map (fun q => q.relabel Sum.inl)
  change Derivation body Theta (psi.relabel Sum.inl)
  have hw : Nonempty (Derivation body Theta (imageMatrix raw param node)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (next (alpha ⊕ Fin 1) Sum.inl Theta (.var (.inr 0)) (by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)) (andLeft hw) (andRight hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageEliminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageEliminationProof
