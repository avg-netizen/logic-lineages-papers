module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
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
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename graph5Subst)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseDirectedRounds (roundsTape)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePassWindowTargets (allWindow)
open NumberedWindowInternalSparsePassWindowSyntaxProof (allSubst)

attribute [local irreducible] programGraph

def safe (X : Program 2) (W : Program 3) {α : Type} (fuel vertices ctx ty seed : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((roundGraph (edge4 X W) out (fuel.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j)).imp (allWindow W (ctx.relabel j) (ty.relabel j) out))

theorem roundRename {α β : Type} (E : Program 4) (out fuel vertices ctx ty seed : OTerm α) (j : α → β) :
    (roundGraph E out fuel vertices ctx ty seed).relabel j = roundGraph E (out.relabel j)
      (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [roundGraph,roundsTape,graph5Rename]

theorem roundSubst {α β : Type} (E : Program 4) (out fuel vertices ctx ty seed : OTerm α) (ts : α → OTerm β) :
    (roundGraph E out fuel vertices ctx ty seed).subst (fun a => emb (ts a)) =
      roundGraph E (out.subst ts) (fuel.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) := by
  simp only [roundGraph,roundsTape,graph5Subst]

theorem safeSubst {α β : Type} (X : Program 2) (W : Program 3) (fuel vertices ctx ty seed : OTerm α)
    (ts : α → OTerm β) : (safe X W fuel vertices ctx ty seed).subst (fun a => emb (ts a)) =
      safe X W (fuel.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) := by
  simp only [safe,allEmbeddedSubst,impSubst,roundSubst,allSubst,liftTermSubst]
  rfl

theorem safeRename {α β : Type} (X : Program 2) (W : Program 3) (fuel vertices ctx ty seed : OTerm α)
    (j : α → β) : (safe X W fuel vertices ctx ty seed).relabel j =
      safe X W (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (safe X W fuel vertices ctx ty seed).subst (fun a => emb (.var (j a))) = _
  rw [safeSubst]
  simp only [termRelabelAsSubst]

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (X : Program 2) (W : Program 3) (fuel vertices ctx ty seed out : OTerm α)
    (proof : Nonempty (Derivation body Γ (safe X W fuel vertices ctx ty seed)))
    (run : Nonempty (Derivation body Γ (roundGraph (edge4 X W) out fuel vertices ctx ty seed))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty out)) := by
  obtain ⟨d⟩ := proof
  obtain ⟨r⟩ := run
  have atOut := Derivation.universalElimination (emb out) d
  simp only [instantiate,bindEmbedding,impSubst,roundSubst,allSubst,liftBind,varBind] at atOut
  exact ⟨Derivation.implicationElimination atOut r⟩

theorem introduce {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (X : Program 2) (W : Program 3) (fuel vertices ctx ty seed : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (roundGraph (edge4 X W) out (fuel.relabel j) (vertices.relabel j)
        (ctx.relabel j) (ty.relabel j) (seed.relabel j))) →
      Nonempty (Derivation body Δ (allWindow W (ctx.relabel j) (ty.relabel j) out))) :
    Nonempty (Derivation body Γ (safe X W fuel vertices ctx ty seed)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let R := roundGraph (edge4 X W) out (fuel.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  let Δ := R :: Γ.map weaken
  obtain ⟨result⟩ := each _ j Δ out (fun p h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
