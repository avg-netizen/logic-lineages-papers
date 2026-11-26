module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerTransportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerBindingProof
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
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverAuxLayerTransportTargets

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

private theorem rowSubst (K T key d c f a : OTerm α) (s : α → OTerm β) :
    (auxOriginRow K T key d c f a).subst (fun x => emb (s x)) =
      auxOriginRow (K.subst s) (T.subst s) (key.subst s)
        (d.subst s) (c.subst s) (f.subst s) (a.subst s) := by
  simp only [auxOriginRow,conjunctionSubst,memberSubst,eqnSubst,auxiliaryTerm,rawConsSubst,zSubst,numeralSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (K : α → Term β) :
    (block phi).subst K = block (phi.subst (Sum.elim (fun child => (K child).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem originSubst (K T key : OTerm α) (s : α → OTerm β) :
    (auxOrigin K T key).subst (fun x => emb (s x)) =
      auxOrigin (K.subst s) (T.subst s) (key.subst s) := by
  unfold auxOrigin auxOriginMatrix
  rw [blockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem originRename (K T key : OTerm α) (j : α → β) :
    (auxOrigin K T key).relabel j =
      auxOrigin (K.relabel j) (T.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (auxOrigin K T key).subst (fun x => emb (.var (j x))) = _
  rw [originSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (K T key d c f a : OTerm α)
    (atWitness : Nonempty (Derivation body Γ (auxOriginRow K T key d c f a))) :
    Nonempty (Derivation body Γ (auxOrigin K T key)) := by
  let ws : Fin 4 → OTerm α := ![d,c,f,a]
  apply actualFiniteExistentialIntroduction body α 4 Γ _ (fun i => emb (ws i))
  have he : Sum.elim Term.var (fun i => emb (ws i)) = (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold auxOriginMatrix
  rw [rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  exact atWitness

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLayerBindingProof
