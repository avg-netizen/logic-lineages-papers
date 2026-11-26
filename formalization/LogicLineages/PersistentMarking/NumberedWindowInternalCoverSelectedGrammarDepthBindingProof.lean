module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalClosedProgramsBindingProof
  (actualFiniteUniversalIntroduction actualFiniteUniversalElimination)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets
open NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof (depthWitness)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Build the actual object motive, discharging assumptions about
arbitrary observed values rather than choosing closed numerical values. -/
theorem buildDepth (d D H K M : OTerm α)
    (point : ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
      (old oldTerms oldArgs next nextTerms nextArgs : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (observed (d.relabel j) (H.relabel j) (K.relabel j)
        (M.relabel j) old oldTerms oldArgs)) →
      Nonempty (Derivation body Δ (observed (D.relabel j) (H.relabel j) (K.relabel j)
        (M.relabel j) next nextTerms nextArgs)) →
      Nonempty (Derivation body Δ (pairInclusion oldTerms nextTerms oldArgs nextArgs))) :
    Nonempty (Derivation body Γ (depthAt d D H K M)) := by
  apply actualFiniteUniversalIntroduction body α 6 Γ (depthMatrix d D H K M)
  let j : α → α ⊕ Fin 6 := Sum.inl
  let v : Fin 6 → OTerm (α ⊕ Fin 6) := fun n => .var (.inr n)
  let L := observed (d.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) (v 0) (v 1) (v 2)
  let R := observed (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) (v 3) (v 4) (v 5)
  let Δ := (L ⊓ R) :: Γ.map (fun p => p.relabel j)
  have obs : Derivation body Δ (L ⊓ R) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := point _ j Δ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft obs⟩ ⟨Derivation.conjunctionRight obs⟩
  exact ⟨Derivation.implicationIntroduction result⟩

theorem consumeDepth (d D H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (h : Nonempty (Derivation body Γ (depthAt d D H K M)))
    (small : Nonempty (Derivation body Γ (observed d H K M old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed D H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  let w : Fin 6 → OTerm α := ![old,oldTerms,oldArgs,next,nextTerms,nextArgs]
  have law := actualFiniteUniversalElimination body α 6 Γ (depthMatrix d D H K M)
    (fun i => emb (w i)) h
  rw [depthWitness] at law
  obtain ⟨law⟩ := law
  obtain ⟨small⟩ := small
  obtain ⟨large⟩ := large
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction small large)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
