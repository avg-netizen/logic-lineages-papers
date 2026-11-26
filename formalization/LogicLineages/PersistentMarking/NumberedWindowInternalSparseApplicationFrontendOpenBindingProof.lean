module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction actualFiniteExistentialElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveHeadDecompositionBlockBindingProof (blockRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportRename auxiliaryRename)
open NumberedWindowInternalSparseApplicationFrontendTargets (applicationRow parsedApplicationInputs)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
  (inputsRename inputsSubst auxiliarySubst outputReportSubst)

abbrev row {α : Type} (least : Program 3) (f u y c r d e l k : OTerm α) : Formula α :=
  parsedApplicationInputs f u c r d e l k ⊓ outputReport least c e (auxiliaryTerm d e l k) y

abbrev someRow {α : Type} (least : Program 3) (f u y : OTerm α) : Formula α :=
  block (applicationRow least f u y)

theorem rowRename {α β : Type} (least : Program 3) (f u y c r d e l k : OTerm α) (j : α → β) :
    (row least f u y c r d e l k).relabel j =
      row least (f.relabel j) (u.relabel j) (y.relabel j) (c.relabel j) (r.relabel j)
        (d.relabel j) (e.relabel j) (l.relabel j) (k.relabel j) := by
  simp only [row,conjunctionRename,inputsRename,reportRename,auxiliaryRename]

theorem someRowRename {α β : Type} (least : Program 3) (f u y : OTerm α) (j : α → β) :
    (someRow least f u y).relabel j = someRow least (f.relabel j) (u.relabel j) (y.relabel j) := by
  simp only [someRow,blockRename]
  apply congrArg (fun p : Formula (β ⊕ Fin 6) => block p)
  let h : α → α ⊕ Fin 6 := Sum.inl
  change (row least (f.relabel h) (u.relabel h) (y.relabel h)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).relabel
      (Sum.map j id) = applicationRow least (f.relabel j) (u.relabel j) (y.relabel j)
  rw [rowRename]
  simp only [applicationRow,row,h,Term.relabel_relabel,Term.relabel] <;> rfl

private theorem witnessLift {α : Type} (n : OTerm α) (xs : Fin 6 → OTerm α) :
    (n.relabel Sum.inl).subst (Sum.elim Term.var xs) = n := by
  rw [termRelabelSubst]
  exact termSubstVar n

private abbrev values {α : Type} (c r d e l k : OTerm α) : Fin 6 → OTerm α := ![c,r,d,e,l,k]

private theorem rowWitness {α : Type} (least : Program 3) (f u y c r d e l k : OTerm α) :
    (applicationRow least f u y).subst (Sum.elim Term.var (fun i => emb (values c r d e l k i))) =
      row least f u y c r d e l k := by
  let xs := values c r d e l k
  have h : (Sum.elim Term.var (fun i => emb (xs i))) = (fun a => emb (Sum.elim Term.var xs a)) := by
    funext a
    cases a <;> rfl
  change (applicationRow least f u y).subst (Sum.elim Term.var (fun i => emb (xs i))) = _
  rw [h]
  simp only [applicationRow,row,conjunctionSubst,inputsSubst,outputReportSubst,auxiliarySubst,
    witnessLift,Term.subst,Sum.elim_inr] <;> rfl

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem supply (least : Program 3) (f u y c r d e l k : OTerm α)
    (known : Nonempty (Derivation body Γ (row least f u y c r d e l k))) :
    Nonempty (Derivation body Γ (someRow least f u y)) := by
  apply actualFiniteExistentialIntroduction body α 6 Γ (applicationRow least f u y)
    (fun i => emb (values c r d e l k i))
  rw [rowWitness]
  exact known

theorem rowCases (least : Program 3) (f u y : OTerm α) (goal : Formula α)
    (known : Nonempty (Derivation body Γ (someRow least f u y)))
    (k : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c r d e l a : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (row least (f.relabel j) (u.relabel j) (y.relabel j) c r d e l a)) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  let j : α → α ⊕ Fin 6 := Sum.inl
  let current := applicationRow least f u y
  let Δ := current :: Γ.map (fun p => p.relabel j)
  apply actualFiniteExistentialElimination body α 6 Γ current goal known
  have hJ (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have r : Nonempty (Derivation body Δ current) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact k (α ⊕ Fin 6) j Δ (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
    (.var (.inr 4)) (.var (.inr 5)) hJ r

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenBindingProof
