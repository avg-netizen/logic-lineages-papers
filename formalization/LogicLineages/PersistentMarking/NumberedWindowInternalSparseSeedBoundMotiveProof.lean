module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open SourceComputabilityFormulaSupportProof (allOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename roundSubst)

attribute [local irreducible] programGraph

def seedAt (E : Program 4) {α : Type} (fuel vertices ctx ty seed : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((roundGraph E out (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j)).imp (memberGraph out (seed.relabel j)))

theorem seedAtSubst {α β : Type} (E : Program 4) (fuel vertices ctx ty seed : OTerm α)
    (ts : α → OTerm β) : (seedAt E fuel vertices ctx ty seed).subst (fun a => emb (ts a)) =
      seedAt E (fuel.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) := by
  simp only [seedAt,allEmbeddedSubst,impSubst,roundSubst,memberSubst,liftTermSubst]
  rfl

theorem seedAtRename {α β : Type} (E : Program 4) (fuel vertices ctx ty seed : OTerm α)
    (j : α → β) : (seedAt E fuel vertices ctx ty seed).relabel j =
      seedAt E (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (seedAt E fuel vertices ctx ty seed).subst (fun a => emb (.var (j a))) = _
  rw [seedAtSubst]
  simp only [termRelabelAsSubst]

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (fuel vertices ctx ty seed out : OTerm α)
    (proof : Nonempty (Derivation body Γ (seedAt E fuel vertices ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph E out fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (memberGraph out seed)) := by
  obtain ⟨d⟩ := proof
  obtain ⟨r⟩ := run
  have atOut := Derivation.universalElimination (emb out) d
  simp only [instantiate,bindEmbedding,impSubst,roundSubst,memberSubst,liftBind,varBind] at atOut
  exact ⟨Derivation.implicationElimination atOut r⟩

theorem introduce {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (fuel vertices ctx ty seed : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (roundGraph E out (fuel.relabel j) (vertices.relabel j)
        (ctx.relabel j) (ty.relabel j) (seed.relabel j))) →
      Nonempty (Derivation body Δ (memberGraph out (seed.relabel j)))) :
    Nonempty (Derivation body Γ (seedAt E fuel vertices ctx ty seed)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let R := roundGraph E out (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  let Δ := R :: Γ.map weaken
  obtain ⟨result⟩ := each _ j Δ out (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedBoundMotiveProof
