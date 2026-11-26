module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBinderTransportProof (actualUniversalRenaming)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTermSubst allEmbeddedSubst programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding bindTerm liftBind varBind sucRelabel sucSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename pairSubst)

/-- Matrix of the shift motive: the bound variable is the common output. -/
def shiftMatrix {α : Type} (p other : Program 3) (fuel start next o : OTerm α) : Formula α :=
  (programGraph (iterateState p other) o ![fuel,next]).imp
    (programGraph (iterateState p other) o ![suc fuel,start])

def shiftMotive {α : Type} (p other : Program 3) (fuel start next : OTerm α) : Formula α :=
  allOne (shiftMatrix p other (fuel.relabel Sum.inl) (start.relabel Sum.inl)
    (next.relabel Sum.inl) (.var (.inr 0)))

theorem shiftMatrixRename {α β : Type} (p other : Program 3) (fuel start next o : OTerm α)
    (j : α → β) :
    (shiftMatrix p other fuel start next o).relabel j =
      shiftMatrix p other (fuel.relabel j) (start.relabel j) (next.relabel j) (o.relabel j) := by
  change ((programGraph (iterateState p other) o ![fuel,next]).relabel j).imp
    ((programGraph (iterateState p other) o ![suc fuel,start]).relabel j) = _
  rw [programRename,programRename,pairRename,pairRename,sucRelabel]
  rfl

theorem shiftMatrixSubst {α β : Type} (p other : Program 3) (fuel start next o : OTerm α)
    (ts : α → OTerm β) :
    (shiftMatrix p other fuel start next o).subst (fun a => emb (ts a)) =
      shiftMatrix p other (fuel.subst ts) (start.subst ts) (next.subst ts) (o.subst ts) := by
  change ((programGraph (iterateState p other) o ![fuel,next]).subst (fun a => emb (ts a))).imp
    ((programGraph (iterateState p other) o ![suc fuel,start]).subst (fun a => emb (ts a))) = _
  rw [programSubst,programSubst,pairSubst,pairSubst,sucSubst]
  rfl

theorem shiftMotiveRename {α β : Type} (p other : Program 3) (fuel start next : OTerm α)
    (j : α → β) :
    (shiftMotive p other fuel start next).relabel j =
      shiftMotive p other (fuel.relabel j) (start.relabel j) (next.relabel j) := by
  unfold shiftMotive
  rw [actualUniversalRenaming,shiftMatrixRename]
  simp only [Term.relabel_relabel]
  rfl

theorem shiftMotiveSubst {α β : Type} (p other : Program 3) (fuel start next : OTerm α)
    (ts : α → OTerm β) :
    (shiftMotive p other fuel start next).subst (fun a => emb (ts a)) =
      shiftMotive p other (fuel.subst ts) (start.subst ts) (next.subst ts) := by
  unfold shiftMotive
  rw [allEmbeddedSubst,shiftMatrixSubst,liftTermSubst,liftTermSubst,liftTermSubst]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem shiftMotiveIntro (p other : Program 3) (fuel start next : OTerm α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (o : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (programGraph (iterateState p other) o ![fuel.relabel j,next.relabel j])) →
      Nonempty (Derivation body Δ
        (programGraph (iterateState p other) o ![suc (fuel.relabel j),start.relabel j]))) :
    Nonempty (Derivation body Γ (shiftMotive p other fuel start next)) := by
  let o : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let g : Formula (α ⊕ Fin 1) :=
    programGraph (iterateState p other) o ![fuel.relabel Sum.inl,next.relabel Sum.inl]
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (g :: Γ.map weaken) o
    (fun φ hφ => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,hφ,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

theorem shiftMotiveApply (p other : Program 3) (fuel start next o : OTerm α)
    (hm : Nonempty (Derivation body Γ (shiftMotive p other fuel start next)))
    (hg : Nonempty (Derivation body Γ (programGraph (iterateState p other) o ![fuel,next]))) :
    Nonempty (Derivation body Γ (programGraph (iterateState p other) o ![suc fuel,start])) := by
  obtain ⟨dm⟩ := hm
  obtain ⟨dg⟩ := hg
  let M : Formula (α ⊕ Fin 1) := shiftMatrix p other (fuel.relabel Sum.inl)
    (start.relabel Sum.inl) (next.relabel Sum.inl) (.var (.inr 0))
  have dm' : Derivation body Γ (allOne M) := dm
  have e : instantiate M (emb o) = shiftMatrix p other fuel start next o := by
    simp only [M,instantiate,bindEmbedding,shiftMatrixSubst,liftBind,varBind]
  have h := Derivation.universalElimination (emb o) dm'
  rw [e] at h
  exact ⟨Derivation.implicationElimination h dg⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShiftMotiveProof
