module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseFieldInductionTargets (atCode atIndex)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveTerminalityTargets
open NumberedWindowInternalSparsePositiveTerminalityUniformBindingProof (row uniformSubst uniformRename)

def motive {α : Type} (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0))

theorem motiveAt {α : Type} (raw : Program 5) (least : Program 3) (ctx ty cert : OTerm α) :
    atCode (motive raw least ctx ty) cert = uniformAt raw least ctx ty cert := by
  simp only [atCode,motive,instantiate,bindEmbedding,uniformSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (raw : Program 5) (least : Program 3) (ctx ty : OTerm α) (i : Fin 3) :
    atIndex (motive raw least ctx ty) i =
      uniformAt raw least (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr i)) := by
  unfold atIndex motive
  rw [uniformRename]
  simp only [Term.relabel_relabel]
  rfl

abbrev rowFuel {α : Type} : OTerm (α ⊕ Fin 3) := .var (.inr 0)
abbrev rowCurrent {α : Type} : OTerm (α ⊕ Fin 3) := .var (.inr 1)
abbrev rowOut {α : Type} : OTerm (α ⊕ Fin 3) := .var (.inr 2)
abbrev rowLift {α : Type} (t : OTerm α) : OTerm (α ⊕ Fin 3) := t.relabel Sum.inl

theorem introUniform {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty cert : OTerm α)
    (k : ∀ (Δ : List (Formula (α ⊕ Fin 3))),
      (∀ p ∈ Γ, p.relabel Sum.inl ∈ Δ) →
      Nonempty (Derivation body Δ (ltF (rowLift cert) (suc rowFuel))) →
      Nonempty (Derivation body Δ (loopGraph raw least rowOut rowFuel
        (rowLift ctx) (rowLift ty) rowCurrent (rowLift cert))) →
      Nonempty (Derivation body Δ (terminalScratch rowOut))) :
    Nonempty (Derivation body Γ (uniformAt raw least ctx ty cert)) := by
  apply actualFiniteUniversalIntroduction body α 3 Γ (row raw least ctx ty cert)
  let a := ltF (rowLift cert) (suc rowFuel) ⊓
    loopGraph raw least rowOut rowFuel (rowLift ctx) (rowLift ty) rowCurrent (rowLift cert)
  let Δ := a :: Γ.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel Sum.inl ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have given : Derivation body Δ a := Derivation.hypothesis List.mem_cons_self
  obtain ⟨d⟩ := k Δ hJ ⟨Derivation.conjunctionLeft given⟩ ⟨Derivation.conjunctionRight given⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityMotiveProof
