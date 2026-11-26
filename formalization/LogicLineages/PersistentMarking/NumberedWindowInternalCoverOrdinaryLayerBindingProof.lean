module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerBindingProof
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
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverOrdinaryLayerTargets

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

private theorem rowSubst (tag : Nat) (K children key ty child : OTerm α) (s : α → OTerm β) :
    (taggedOriginRow tag K children key ty child).subst (fun x => emb (s x)) =
      taggedOriginRow tag (K.subst s) (children.subst s) (key.subst s) (ty.subst s) (child.subst s) := by
  simp only [taggedOriginRow,taggedTerm,conjunctionSubst,memberSubst,eqnSubst,namedTerm,rawConsSubst,zSubst,numeralSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (K : α → Term β) :
    (block phi).subst K = block (phi.subst (Sum.elim (fun child => (K child).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem pairSubst (tag : Nat) (K children key : OTerm α) (s : α → OTerm β) :
    (taggedOrigin tag K children key).subst (fun x => emb (s x)) =
      taggedOrigin tag (K.subst s) (children.subst s) (key.subst s) := by
  unfold taggedOrigin taggedOriginMatrix
  rw [blockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem originRename (tag : Nat) (K children key : OTerm α) (j : α → β) :
    (taggedOrigin tag K children key).relabel j =
      taggedOrigin tag (K.relabel j) (children.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (taggedOrigin tag K children key).subst (fun child => emb (.var (j child))) = _
  rw [pairSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (tag : Nat) (K children key ty child : OTerm α)
    (atWitness : Nonempty (Derivation body Γ (taggedOriginRow tag K children key ty child))) :
    Nonempty (Derivation body Γ (taggedOrigin tag K children key)) := by
  let ws : Fin 2 → OTerm α := ![ty,child]
  apply actualFiniteExistentialIntroduction body α 2 Γ _ (fun i => emb (ws i))
  have he : Sum.elim Term.var (fun i => emb (ws i)) = (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold taggedOriginMatrix
  rw [rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  exact atWitness

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerBindingProof
