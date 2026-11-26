module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationMotiveProof
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
open NumberedWindowInternalSparseRawRunShapeMotiveProof (pairRename pairSubst)

def tickStep (tick : Program 1) : Program 3 :=
  .composition tick (fun _ : Fin 1 => .projection 1)

def tickLoop (tick : Program 1) : Program 2 := .recursion (.projection 0) (tickStep tick)

/-- Matrix of the shift motive: the bound variable is the common output. -/
def shiftMatrix {α : Type} (tick : Program 1) (fuel start next o : OTerm α) : Formula α :=
  (programGraph (tickLoop tick) o ![fuel,next]).imp
    (programGraph (tickLoop tick) o ![suc fuel,start])

def shiftMotive {α : Type} (tick : Program 1) (fuel start next : OTerm α) : Formula α :=
  allOne (shiftMatrix tick (fuel.relabel Sum.inl) (start.relabel Sum.inl)
    (next.relabel Sum.inl) (.var (.inr 0)))

theorem shiftMatrixRename {α β : Type} (tick : Program 1) (fuel start next o : OTerm α)
    (j : α → β) :
    (shiftMatrix tick fuel start next o).relabel j =
      shiftMatrix tick (fuel.relabel j) (start.relabel j) (next.relabel j) (o.relabel j) := by
  change ((programGraph (tickLoop tick) o ![fuel,next]).relabel j).imp
    ((programGraph (tickLoop tick) o ![suc fuel,start]).relabel j) = _
  rw [programRename,programRename,pairRename,pairRename,sucRelabel]
  rfl

theorem shiftMatrixSubst {α β : Type} (tick : Program 1) (fuel start next o : OTerm α)
    (ts : α → OTerm β) :
    (shiftMatrix tick fuel start next o).subst (fun a => emb (ts a)) =
      shiftMatrix tick (fuel.subst ts) (start.subst ts) (next.subst ts) (o.subst ts) := by
  change ((programGraph (tickLoop tick) o ![fuel,next]).subst (fun a => emb (ts a))).imp
    ((programGraph (tickLoop tick) o ![suc fuel,start]).subst (fun a => emb (ts a))) = _
  rw [programSubst,programSubst,pairSubst,pairSubst,sucSubst]
  rfl

theorem shiftMotiveRename {α β : Type} (tick : Program 1) (fuel start next : OTerm α)
    (j : α → β) :
    (shiftMotive tick fuel start next).relabel j =
      shiftMotive tick (fuel.relabel j) (start.relabel j) (next.relabel j) := by
  unfold shiftMotive
  rw [actualUniversalRenaming,shiftMatrixRename]
  simp only [Term.relabel_relabel]
  rfl

theorem shiftMotiveSubst {α β : Type} (tick : Program 1) (fuel start next : OTerm α)
    (ts : α → OTerm β) :
    (shiftMotive tick fuel start next).subst (fun a => emb (ts a)) =
      shiftMotive tick (fuel.subst ts) (start.subst ts) (next.subst ts) := by
  unfold shiftMotive
  rw [allEmbeddedSubst,shiftMatrixSubst,liftTermSubst,liftTermSubst,liftTermSubst]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem shiftMotiveIntro (tick : Program 1) (fuel start next : OTerm α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (o : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (programGraph (tickLoop tick) o ![fuel.relabel j,next.relabel j])) →
      Nonempty (Derivation body Δ
        (programGraph (tickLoop tick) o ![suc (fuel.relabel j),start.relabel j]))) :
    Nonempty (Derivation body Γ (shiftMotive tick fuel start next)) := by
  let o : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let g : Formula (α ⊕ Fin 1) :=
    programGraph (tickLoop tick) o ![fuel.relabel Sum.inl,next.relabel Sum.inl]
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (g :: Γ.map weaken) o
    (fun φ hφ => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,hφ,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

theorem shiftMotiveApply (tick : Program 1) (fuel start next o : OTerm α)
    (hm : Nonempty (Derivation body Γ (shiftMotive tick fuel start next)))
    (hg : Nonempty (Derivation body Γ (programGraph (tickLoop tick) o ![fuel,next]))) :
    Nonempty (Derivation body Γ (programGraph (tickLoop tick) o ![suc fuel,start])) := by
  obtain ⟨dm⟩ := hm
  obtain ⟨dg⟩ := hg
  let M : Formula (α ⊕ Fin 1) := shiftMatrix tick (fuel.relabel Sum.inl)
    (start.relabel Sum.inl) (next.relabel Sum.inl) (.var (.inr 0))
  have dm' : Derivation body Γ (allOne M) := dm
  have e : instantiate M (emb o) = shiftMatrix tick fuel start next o := by
    simp only [M,instantiate,bindEmbedding,shiftMatrixSubst,liftBind,varBind]
  have h := Derivation.universalElimination (emb o) dm'
  rw [e] at h
  exact ⟨Derivation.implicationElimination h dg⟩

#print axioms shiftMotiveRename
#print axioms shiftMotiveSubst
#print axioms shiftMotiveIntro
#print axioms shiftMotiveApply
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickIterationMotiveProof
