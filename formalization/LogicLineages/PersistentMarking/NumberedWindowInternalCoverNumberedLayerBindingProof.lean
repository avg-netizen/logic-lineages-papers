module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionSyntaxProof (bindSubst exsSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialIntroduction)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqnSubst sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons z)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverNumberedLayerTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}

private theorem numeralSubst (n : Nat) (ts : α → OTerm β) :
    (numeral n : OTerm α).subst ts = numeral n := by
  induction n with
  | zero => exact zSubst ts
  | succ n ih => simpa only [numeral,sucSubst] using congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

private theorem rawConsSubst (x y : OTerm α) (ts : α → OTerm β) :
    (rawCons x y).subst ts = rawCons (x.subst ts) (y.subst ts) := by
  unfold rawCons pairTerm
  simp only [sucSubst,addSubst,mulSubst]

private theorem rowSubst (H K ids args key h ty k l r : OTerm α) (s : α → OTerm β) :
    (numberedOriginRow H K ids args key h ty k l r).subst (fun x => emb (s x)) =
      numberedOriginRow (H.subst s) (K.subst s) (ids.subst s) (args.subst s) (key.subst s)
        (h.subst s) (ty.subst s) (k.subst s) (l.subst s) (r.subst s) := by
  simp only [numberedOriginRow,conjunctionSubst,memberSubst,eqnSubst,numberedTerm,rawConsSubst,zSubst,numeralSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (K : α → Term β) :
    (block phi).subst K = block (phi.subst (Sum.elim (fun child => (K child).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem originSubst (H K ids args key : OTerm α) (s : α → OTerm β) :
    (numberedOrigin H K ids args key).subst (fun x => emb (s x)) =
      numberedOrigin (H.subst s) (K.subst s) (ids.subst s) (args.subst s) (key.subst s) := by
  unfold numberedOrigin numberedOriginMatrix
  rw [blockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem originRename (H K ids args key : OTerm α) (j : α → β) :
    (numberedOrigin H K ids args key).relabel j =
      numberedOrigin (H.relabel j) (K.relabel j) (ids.relabel j) (args.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (numberedOrigin H K ids args key).subst (fun x => emb (.var (j x))) = _
  rw [originSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (H K ids args key h ty k l r : OTerm α)
    (atWitness : Nonempty (Derivation body Γ (numberedOriginRow H K ids args key h ty k l r))) :
    Nonempty (Derivation body Γ (numberedOrigin H K ids args key)) := by
  let ws : Fin 5 → OTerm α := ![h,ty,k,l,r]
  apply actualFiniteExistentialIntroduction body α 5 Γ _ (fun i => emb (ws i))
  have he : Sum.elim Term.var (fun i => emb (ws i)) = (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold numberedOriginMatrix
  rw [rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  exact atWitness

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerBindingProof
