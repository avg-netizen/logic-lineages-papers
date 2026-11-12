module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalIntroductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalTwoDeletionInternalDefinitions OriginalTwoDeletionInternalBindingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntroFrom (p : Program 3) (raw : OTerm alpha)
    (step : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
      (a b i j upper lower left right : OTerm beta),
      (∀ r ∈ Delta, r.relabel rho ∈ Theta) →
      Nonempty (Derivation body Theta (fields p (raw.relabel rho) a b i j upper lower left right)) →
      Nonempty (Derivation body Theta (equal left right))) :
    Nonempty (Derivation body Delta (AtRaw p raw)) := by
  let a : OTerm (alpha ⊕ Fin 8) := .var (.inr 0)
  let b : OTerm (alpha ⊕ Fin 8) := .var (.inr 1)
  let i : OTerm (alpha ⊕ Fin 8) := .var (.inr 2)
  let j : OTerm (alpha ⊕ Fin 8) := .var (.inr 3)
  let upper : OTerm (alpha ⊕ Fin 8) := .var (.inr 4)
  let lower : OTerm (alpha ⊕ Fin 8) := .var (.inr 5)
  let left : OTerm (alpha ⊕ Fin 8) := .var (.inr 6)
  let right : OTerm (alpha ⊕ Fin 8) := .var (.inr 7)
  let A := fields p (raw.relabel Sum.inl) a b i j upper lower left right
  let Theta := A :: Delta.map (fun r => r.relabel Sum.inl)
  obtain ⟨h⟩ := step (alpha ⊕ Fin 8) Sum.inl Theta a b i j upper lower left right
    (by intro r hr; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact atRawIntro p raw ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalIntroductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalIntroductionProof
