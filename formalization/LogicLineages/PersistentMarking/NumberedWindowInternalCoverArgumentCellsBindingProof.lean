module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsBindingProof
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
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqnSubst sucSubst eqnRelabel zRelabel)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open ID1Completion.InternalBetaBoundaryProof (supRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverArgumentCellsTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}

private theorem rawConsSubst (x y : OTerm α) (ts : α → OTerm β) :
    (rawCons x y).subst ts = rawCons (x.subst ts) (y.subst ts) := by
  unfold rawCons pairTerm
  simp only [sucSubst,addSubst,mulSubst]

private theorem rowSubst (ts ars key q a : OTerm α) (s : α → OTerm β) :
    (cellOriginRow ts ars key q a).subst (fun x => emb (s x)) =
      cellOriginRow (ts.subst s) (ars.subst s) (key.subst s) (q.subst s) (a.subst s) := by
  simp only [cellOriginRow,conjunctionSubst,memberSubst,eqnSubst,rawConsSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (ts : α → Term β) :
    (block phi).subst ts = block (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem pairSubst (ts ars key : OTerm α) (s : α → OTerm β) :
    (cellPairOrigin ts ars key).subst (fun x => emb (s x)) =
      cellPairOrigin (ts.subst s) (ars.subst s) (key.subst s) := by
  unfold cellPairOrigin cellOriginMatrix
  rw [blockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem pairRename (ts ars key : OTerm α) (j : α → β) :
    (cellPairOrigin ts ars key).relabel j =
      cellPairOrigin (ts.relabel j) (ars.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (cellPairOrigin ts ars key).subst (fun a => emb (.var (j a))) = _
  rw [pairSubst]
  simp only [← termRelabelAsSubst]

theorem originRename (ts ars key : OTerm α) (j : α → β) :
    (cellOrigin ts ars key).relabel j =
      cellOrigin (ts.relabel j) (ars.relabel j) (key.relabel j) := by
  simp only [cellOrigin,supRename,eqnRelabel,zRelabel,pairRename]

theorem introduce (ts ars key q a : OTerm α)
    (atWitness : Nonempty (Derivation body Γ (cellOriginRow ts ars key q a))) :
    Nonempty (Derivation body Γ (cellPairOrigin ts ars key)) := by
  let ws : Fin 2 → OTerm α := ![q,a]
  apply actualFiniteExistentialIntroduction body α 2 Γ _ (fun i => emb (ws i))
  have he : Sum.elim Term.var (fun i => emb (ws i)) = (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold cellOriginMatrix
  rw [rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  exact atWitness

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsBindingProof
