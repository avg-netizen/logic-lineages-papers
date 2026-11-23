module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsMotiveProof
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
open NumberedWindowInternalScratchInclusionThinProof (included)
open NumberedWindowInternalScratchInclusionThinProof (includedSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename roundSubst)

attribute [local irreducible] programGraph

def inside (E : Program 4) {α : Type} (fuel vertices ctx ty seed upper : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((roundGraph E out (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j)).imp (included out (upper.relabel j)))

theorem insideSubst {α β : Type} (E : Program 4) (fuel vertices ctx ty seed upper : OTerm α)
    (ts : α → OTerm β) : (inside E fuel vertices ctx ty seed upper).subst (fun a => emb (ts a)) =
      inside E (fuel.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (upper.subst ts) := by
  simp only [inside,allEmbeddedSubst,impSubst,roundSubst,includedSubst,liftTermSubst]
  rfl

theorem insideRename {α β : Type} (E : Program 4) (fuel vertices ctx ty seed upper : OTerm α)
    (j : α → β) : (inside E fuel vertices ctx ty seed upper).relabel j =
      inside E (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (upper.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (inside E fuel vertices ctx ty seed upper).subst (fun a => emb (.var (j a))) = _
  rw [insideSubst]
  simp only [termRelabelAsSubst]

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (fuel vertices ctx ty seed upper out : OTerm α)
    (proof : Nonempty (Derivation body Γ (inside E fuel vertices ctx ty seed upper)))
    (run : Nonempty (Derivation body Γ (roundGraph E out fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (included out upper)) := by
  obtain ⟨d⟩ := proof
  obtain ⟨r⟩ := run
  have atOut := Derivation.universalElimination (emb out) d
  simp only [instantiate,bindEmbedding,impSubst,roundSubst,includedSubst,liftBind,varBind] at atOut
  exact ⟨Derivation.implicationElimination atOut r⟩

theorem introduce {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (fuel vertices ctx ty seed upper : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (roundGraph E out (fuel.relabel j) (vertices.relabel j)
        (ctx.relabel j) (ty.relabel j) (seed.relabel j))) →
      Nonempty (Derivation body Δ (included out (upper.relabel j)))) :
    Nonempty (Derivation body Γ (inside E fuel vertices ctx ty seed upper)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let R := roundGraph E out (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  let Δ := R :: Γ.map weaken
  obtain ⟨result⟩ := each _ j Δ out (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsMotiveProof
