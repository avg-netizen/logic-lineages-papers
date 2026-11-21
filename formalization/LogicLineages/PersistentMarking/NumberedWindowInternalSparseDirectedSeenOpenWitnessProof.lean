module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenWitnessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem introduce (E : Program 4) (code ctx ty w v : OTerm α)
    (member : Nonempty (Derivation body Γ (memberGraph code w)))
    (valid : Nonempty (Derivation body Γ (eqn w v ⊔ acceptEdge E ctx ty w v))) :
    Nonempty (Derivation body Γ (seenWitness E code ctx ty v)) := by
  obtain ⟨member⟩ := member
  obtain ⟨valid⟩ := valid
  rw [witnessUnfold]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb w)
  rw [witnessInstance]
  exact Derivation.conjunctionIntroduction member valid

/-- Choose the actual head, with its real membership graph for this cons. -/
theorem atHead (E : Program 4) (code h tail ctx ty v : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h tail)))
    (valid : Nonempty (Derivation body Γ (eqn h v ⊔ acceptEdge E ctx ty h v))) :
    Nonempty (Derivation body Γ (seenWitness E code ctx ty v)) :=
  introduce E code ctx ty h v (headMember code h tail h cell ⟨refl h⟩) valid

/-- Carry the same existential witness from the physical tail to the
whole cons. Its actual edge/equality proof is preserved unchanged. -/
theorem fromTail (E : Program 4) (code h tail ctx ty v : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h tail)))
    (old : Nonempty (Derivation body Γ (seenWitness E tail ctx ty v))) :
    Nonempty (Derivation body Γ (seenWitness E code ctx ty v)) := by
  obtain ⟨old⟩ := old
  rw [witnessUnfold] at old
  let A := witnessBinder E tail ctx ty v
  let Δ := A :: Γ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hc := renameInto cell j Δ keep
  rw [consGraphRename] at hc
  have row : Derivation body Δ
      (memberGraph (tail.relabel j) w ⊓ (eqn w (v.relabel j) ⊔
        acceptEdge E (ctx.relabel j) (ty.relabel j) w (v.relabel j))) :=
    Derivation.hypothesis List.mem_cons_self
  have member := tailMember (code.relabel j) (h.relabel j) (tail.relabel j) w hc
    ⟨Derivation.conjunctionLeft row⟩
  have hnew := introduce E (code.relabel j) (ctx.relabel j) (ty.relabel j) w (v.relabel j)
    member ⟨Derivation.conjunctionRight row⟩
  rw [← witnessRename E code ctx ty v j] at hnew
  obtain ⟨d⟩ := hnew
  exact ⟨Derivation.existentialElimination old d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenWitnessProof
