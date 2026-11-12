module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalStructuralNodeSizeInternalErasureDefinitions OriginalStructuralNodeSizeInternalErasureBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntroFrom (input : OTerm alpha)
    (step : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
      (d k erased before after : OTerm beta),
      (∀ r ∈ Delta, r.relabel rho ∈ Theta) →
      Nonempty (Derivation body Theta (fields (input.relabel rho) d k erased before after)) →
      Nonempty (Derivation body Theta (equal before after))) :
    Nonempty (Derivation body Delta (AtRaw input)) := by
  let d : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let k : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let erased : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let before : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let after : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields (input.relabel Sum.inl) d k erased before after
  let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
  obtain ⟨h⟩ := step (alpha ⊕ Fin 5) Sum.inl Theta d k erased before after
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact atRawIntro input ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureIntroductionProof
