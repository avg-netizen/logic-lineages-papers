module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst zSubst)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalClosedProgramsBindingProof (introduction elimination)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

/-- Object-level membership inclusion on the literal original scratch
member callback; no numerical lists or external membership reflection. -/
def included {α : Type} (left right : OTerm α) : Formula α :=
  allBlock ((memberGraph (left.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (memberGraph (right.relabel Sum.inl) (.var (.inr (0 : Fin 1)))))

private theorem graphSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) = memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

@[simp] theorem includedSubst {alpha beta : Type} (left right : OrdinaryArithmetic.Term alpha)
    (ts : alpha → OrdinaryArithmetic.Term beta) :
    (included left right).subst (fun a => emb (ts a)) = included (left.subst ts) (right.subst ts) := by
  unfold included
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graphSubst,
    liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem includedRename {alpha beta : Type} (left right : OrdinaryArithmetic.Term alpha)
    (j : alpha → beta) :
    (included left right).relabel j = included (left.relabel j) (right.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (included left right).subst (fun a => emb (.var (j a))) = _
  rw [includedSubst]
  simp only [← termRelabelAsSubst]

theorem eliminate {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (left right candidate : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hm : Nonempty (Derivation body Delta (memberGraph left candidate))) :
    Nonempty (Derivation body Delta (memberGraph right candidate)) := by
  obtain ⟨h⟩ := elimination body alpha 1 Delta _ (fun _ => emb candidate) hi
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb candidate)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => candidate) a)) := by
    funext a
    cases a <;> rfl
  rw [he] at h
  simp only [impSubst,graphSubst,
    witnessLift,Term.subst,Sum.elim_inr] at h
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h hm⟩

theorem introduce {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (left right : OrdinaryArithmetic.Term alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (candidate : OrdinaryArithmetic.Term beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (memberGraph (left.relabel j) candidate)) →
      Nonempty (Derivation body Theta (memberGraph (right.relabel j) candidate))) :
    Nonempty (Derivation body Delta (included left right)) := by
  apply introduction body alpha 1 Delta
  let candidate : OrdinaryArithmetic.Term (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := memberGraph (left.relabel Sum.inl) candidate
  obtain ⟨h⟩ := next (alpha ⊕ Fin 1) Sum.inl
    (A :: Delta.map (fun q => q.relabel Sum.inl)) candidate
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

#print axioms includedSubst
#print axioms includedRename
#print axioms eliminate
#print axioms introduce
end LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
