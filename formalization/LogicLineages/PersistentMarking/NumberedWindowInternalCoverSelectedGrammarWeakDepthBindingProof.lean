module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets (depthAt)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
open NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof (lowerInstance)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem buildLower (D H K M : OTerm α)
    (point : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (d : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (ltF d (suc (D.relabel j)))) →
      Nonempty (Derivation body Δ (depthAt d (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)))) :
    Nonempty (Derivation body Γ (allLower D H K M)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let d : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let L := ltF d (suc (D.relabel j))
  let Δ := L :: Γ.map (fun q => q.relabel j)
  obtain ⟨proof⟩ := point _ j Δ d
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction proof)⟩

theorem useLower (d D H K M : OTerm α)
    (law : Nonempty (Derivation body Γ (allLower D H K M)))
    (weak : Nonempty (Derivation body Γ (ltF d (suc D)))) :
    Nonempty (Derivation body Γ (depthAt d D H K M)) := by
  obtain ⟨law⟩ := law
  obtain ⟨weak⟩ := weak
  have h := Derivation.universalElimination (emb d) law
  rw [lowerInstance] at h
  exact ⟨Derivation.implicationElimination h weak⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof
