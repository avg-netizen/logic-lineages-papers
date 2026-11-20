module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldInductionTargets (atCode atIndex)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt finishAt)
open NumberedWindowInternalSparsePositiveTransitivityTargets
open NumberedWindowInternalSparsePositiveTransitivityBindingProof (row uniformSubst uniformRename)

def motive {α : Type} (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0))

theorem motiveAt {α : Type} (raw : Program 5) (least : Program 3) (ctx ty code : OTerm α) :
    atCode (motive raw least ctx ty) code = uniformAt raw least ctx ty code := by
  simp only [atCode,motive,instantiate,bindEmbedding,uniformSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty : OTerm α) (i : Fin 3) :
    atIndex (motive raw least ctx ty) i =
      uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr i)) := by
  unfold atIndex motive
  rw [uniformRename]
  simp only [Term.relabel_relabel] <;> rfl

abbrev rowSrc {α : Type} : OTerm (α ⊕ Fin 4) := .var (.inr 0)
abbrev rowMid {α : Type} : OTerm (α ⊕ Fin 4) := .var (.inr 1)
abbrev rowSecond {α : Type} : OTerm (α ⊕ Fin 4) := .var (.inr 2)
abbrev rowDst {α : Type} : OTerm (α ⊕ Fin 4) := .var (.inr 3)
abbrev rowLift {α : Type} (u : OTerm α) : OTerm (α ⊕ Fin 4) := u.relabel Sum.inl

theorem introUniform {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty first : OTerm α)
    (k : ∀ (Δ : List (Formula (α ⊕ Fin 4))), (∀ p ∈ Γ, p.relabel Sum.inl ∈ Δ) →
      Nonempty (Derivation body Δ (finishAt raw least (rowLift ctx) (rowLift ty) rowSrc (rowLift first) rowMid)) →
      Nonempty (Derivation body Δ (positiveAt raw least (rowLift ctx) (rowLift ty) rowMid rowSecond rowDst)) →
      Nonempty (Derivation body Δ (supplied raw least (rowLift ctx) (rowLift ty) rowSrc rowDst))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty first)) := by
  apply actualFiniteUniversalIntroduction body α 4 Γ (row raw least ctx ty first)
  let a := finishAt raw least (rowLift ctx) (rowLift ty) rowSrc (rowLift first) rowMid ⊓
    positiveAt raw least (rowLift ctx) (rowLift ty) rowMid rowSecond rowDst
  let Δ := a :: Γ.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel Sum.inl ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have input : Derivation body Δ a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := k Δ hJ ⟨Derivation.conjunctionLeft input⟩ ⟨Derivation.conjunctionRight input⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityMotiveProof
