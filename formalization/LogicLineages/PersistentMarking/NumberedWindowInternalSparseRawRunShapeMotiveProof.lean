module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalBinderTransportProof (actualUniversalRenaming)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalComputabilityApplicationSyntaxProof
  (liftTermSubst allEmbeddedSubst programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding bindTerm liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawRun (iterateState)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename)
open NumberedWindowInternalSparseRawRunShapeLogicProof (goodSubst)

theorem pairRename {α β : Type} (s t : OTerm α) (j : α → β) :
    (fun i : Fin 2 => (![s,t] i).relabel j) = ![s.relabel j,t.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)) i

theorem pairSubst {α β : Type} (s t : OTerm α) (f : α → OTerm β) :
    (fun i : Fin 2 => (![s,t] i).subst f) = ![s.subst f,t.subst f] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a)) i

/-- Matrix of the induction motive: the bound variable is the output. -/
def loopMatrix {α : Type} (p other : Program 3) (fuel start o : OTerm α) : Formula α :=
  (programGraph (iterateState p other) o ![fuel,start]).imp (goodState o)

/-- Internally output-quantified loop invariant at a fixed start. -/
def loopMotive {α : Type} (p other : Program 3) (fuel start : OTerm α) : Formula α :=
  allOne (loopMatrix p other (fuel.relabel Sum.inl) (start.relabel Sum.inl) (.var (.inr 0)))

theorem matrixRename {α β : Type} (p other : Program 3) (fuel start o : OTerm α) (j : α → β) :
    (loopMatrix p other fuel start o).relabel j =
      loopMatrix p other (fuel.relabel j) (start.relabel j) (o.relabel j) := by
  change ((programGraph (iterateState p other) o ![fuel,start]).relabel j).imp
    ((goodState o).relabel j) = _
  rw [programRename,pairRename,goodRename]
  rfl

theorem matrixSubst {α β : Type} (p other : Program 3) (fuel start o : OTerm α)
    (ts : α → OTerm β) :
    (loopMatrix p other fuel start o).subst (fun a => emb (ts a)) =
      loopMatrix p other (fuel.subst ts) (start.subst ts) (o.subst ts) := by
  change ((programGraph (iterateState p other) o ![fuel,start]).subst (fun a => emb (ts a))).imp
    ((goodState o).subst (fun a => emb (ts a))) = _
  rw [programSubst,pairSubst,goodSubst]
  rfl

theorem motiveRename {α β : Type} (p other : Program 3) (fuel start : OTerm α) (j : α → β) :
    (loopMotive p other fuel start).relabel j =
      loopMotive p other (fuel.relabel j) (start.relabel j) := by
  unfold loopMotive
  rw [actualUniversalRenaming,matrixRename]
  simp only [Term.relabel_relabel]
  rfl

theorem motiveSubst {α β : Type} (p other : Program 3) (fuel start : OTerm α)
    (ts : α → OTerm β) :
    (loopMotive p other fuel start).subst (fun a => emb (ts a)) =
      loopMotive p other (fuel.subst ts) (start.subst ts) := by
  unfold loopMotive
  rw [allEmbeddedSubst,matrixSubst,liftTermSubst,liftTermSubst]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Universal introduction at a genuinely fresh output eigenvariable. -/
theorem motiveIntro (p other : Program 3) (fuel start : OTerm α)
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (o : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (programGraph (iterateState p other) o ![fuel.relabel j,start.relabel j])) →
      Nonempty (Derivation body Δ (goodState o))) :
    Nonempty (Derivation body Γ (loopMotive p other fuel start)) := by
  let o : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let g : Formula (α ⊕ Fin 1) :=
    programGraph (iterateState p other) o ![fuel.relabel Sum.inl,start.relabel Sum.inl]
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (g :: Γ.map weaken) o
    (fun φ hφ => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨φ,hφ,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

/-- Universal elimination at an arbitrary supplied output term. -/
theorem motiveApply (p other : Program 3) (fuel start o : OTerm α)
    (hm : Nonempty (Derivation body Γ (loopMotive p other fuel start)))
    (hg : Nonempty (Derivation body Γ (programGraph (iterateState p other) o ![fuel,start]))) :
    Nonempty (Derivation body Γ (goodState o)) := by
  obtain ⟨dm⟩ := hm
  obtain ⟨dg⟩ := hg
  let M : Formula (α ⊕ Fin 1) :=
    loopMatrix p other (fuel.relabel Sum.inl) (start.relabel Sum.inl) (.var (.inr 0))
  have dm' : Derivation body Γ (allOne M) := dm
  have e : instantiate M (emb o) = loopMatrix p other fuel start o := by
    simp only [M,instantiate,bindEmbedding,matrixSubst,liftBind,varBind]
  have h := Derivation.universalElimination (emb o) dm'
  rw [e] at h
  exact ⟨Derivation.implicationElimination h dg⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeMotiveProof
