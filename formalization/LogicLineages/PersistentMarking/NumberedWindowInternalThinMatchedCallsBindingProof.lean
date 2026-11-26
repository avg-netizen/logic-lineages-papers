module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalThinApplicationHopTargets (provided row hopData)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseLeastSubstitutionThinProof (leastSubst)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedSubst suppliedRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem pulledRename {β : Type} (ctx cod parent value : OTerm α) (j : α → β) :
    (pulled C X W s raw ctx cod parent value).relabel j =
    pulled C X W s raw (ctx.relabel j) (cod.relabel j) (parent.relabel j) (value.relabel j) := by
  simp only [pulled,existsRename,conjunctionRename,leastRename,suppliedRename,Term.relabel_relabel,Term.relabel]
  rfl

theorem provideEarlier (ctx cod parent value earlier : OTerm α)
    (found : Derivation body Γ (leastGraph C X W s ctx cod parent earlier))
    (path : Derivation body Γ (supplied raw (packedLeastProgram C X W s) ctx cod earlier value)) :
    Nonempty (Derivation body Γ (pulled C X W s raw ctx cod parent value)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) x ⊓
    supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) x (value.relabel j)
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb earlier)
  simp only [clause,j,x,instantiate,bindEmbedding,conjunctionSubst,leastSubst,suppliedSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction found path

theorem moveTarget (raw : Program 5) (least : Program 3) (ctx cod a r v : OTerm α)
    (same : Derivation body Γ (eqn r v)) (path : Derivation body Γ (supplied raw least ctx cod a r)) :
    Nonempty (Derivation body Γ (supplied raw least ctx cod a v)) := by
  let clause : Formula (α ⊕ Fin 1) := supplied raw least (ctx.relabel Sum.inl) (cod.relabel Sum.inl)
    (a.relabel Sum.inl) (.var (.inr 0))
  have inst (t : OTerm α) : instantiate clause (emb t) = supplied raw least ctx cod a t := by
    simp only [clause,instantiate,bindEmbedding,suppliedSubst,liftBind,varBind]
  exact ⟨(inst v) ▸ Derivation.equalityElimination clause (emb r) (emb v) same ((inst r).symm ▸ path)⟩

theorem hopCases (ctx cod src wr dst : OTerm α) (goal : Formula α)
    (checked : Nonempty (Derivation body Γ (provided C X W s raw ctx cod src wr dst)))
    (finish : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (a b : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (hopData C X W s raw (ctx.relabel j) (cod.relabel j)
        (src.relabel j) (wr.relabel j) (dst.relabel j) a b)) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 2 := Sum.inl
  let clause := row C X W s raw ctx cod src wr dst
  let Δ := clause :: Γ.map (fun q => q.relabel j)
  apply actualFiniteExistentialElimination body α 2 Γ clause goal checked
  exact finish _ j Δ (.var (.inr 0)) (.var (.inr 1))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
#print axioms pulledRename
#print axioms provideEarlier
#print axioms moveTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsBindingProof
