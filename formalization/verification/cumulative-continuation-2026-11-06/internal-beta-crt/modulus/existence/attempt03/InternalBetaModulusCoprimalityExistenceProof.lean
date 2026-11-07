module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityExistenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalCoprimeMultiple InternalCoprimeMultipleSupportProof
open InternalBezoutExistenceTargets InternalBezoutExistenceConsumerProof InternalDivisibilityProductProof
open InternalBetaModulusCoprimality InternalDerivationRenamingSyntaxProof InternalOriginalOrderProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- Symmetry is a derivation in the original arithmetic calculus, in any context. -/
theorem coprimeSymmetry (a b : OTerm α)
    (h : Nonempty (Derivation body Gamma (coprime a b))) :
    Nonempty (Derivation body Gamma (coprime b a)) := by
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let p : Formula (α ⊕ Fin 1) := arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc (.var (.inr 0))) (b.relabel Sum.inl)) ⊓
    arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc (.var (.inr 0))) (a.relabel Sum.inl))
  have hi : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ p :: Gamma.map weaken := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  obtain ⟨hc⟩ := renameInto h Sum.inl (p :: Gamma.map weaken) hi
  have hu := freshUniversal hc
  have hp : Derivation body (p :: Gamma.map weaken) p := Derivation.hypothesis List.mem_cons_self
  exact Derivation.implicationElimination hu
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight hp) (Derivation.conjunctionLeft hp))

theorem actualPositiveMultipleExists : InternalBetaModulusCoprimalityTargets.ActualPositiveMultipleExists := by
  intro body α n
  let t : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have hc : Nonempty (Derivation body [] (coprimeBelow (suc z) t n)) := by
    apply Nonempty.intro
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    simpa only [sucRelabel, zRelabel] using
      (coprimeSymmetry (body := body) (Gamma := _) (suc t) (suc z) (coprimeOne (suc t))).some
  obtain ⟨hi⟩ := InternalCoprimeMultipleProof.actualBoundedCoprimeMultiple body α z n t
  obtain ⟨hc⟩ := hc
  have hm := Derivation.implicationElimination hi hc
  exact ⟨existsMap hm (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityExistenceProof
