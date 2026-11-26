module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
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
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalMultiplicationLawsProof (mulSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverCartesianFoldOriginTargets (hasOrigin originBinder)
open NumberedWindowInternalCoverNamedLeafOriginTargets

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

private theorem rowSubst (b : Bool) (K m key ty i : OTerm α) (ts : α → OTerm β) :
    (NumberedWindowInternalCoverNamedLeafOriginTargets.originRow b K m key ty i).subst (fun x => emb (ts x)) =
      NumberedWindowInternalCoverNamedLeafOriginTargets.originRow b (K.subst ts) (m.subst ts)
        (key.subst ts) (ty.subst ts) (i.subst ts) := by
  simp only [NumberedWindowInternalCoverNamedLeafOriginTargets.originRow,conjunctionSubst,
    memberSubst,orderSubst,eqnSubst,sucSubst,namedTerm,rawConsSubst,zSubst,numeralSubst]

private theorem blockSubst {k : Nat} (phi : Formula (α ⊕ Fin k)) (ts : α → Term β) :
    (block phi).subst ts = block (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl)
        (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem namedOriginSubst (b : Bool) (K m key : OTerm α) (ts : α → OTerm β) :
    (namedOrigin b K m key).subst (fun x => emb (ts x)) =
      namedOrigin b (K.subst ts) (m.subst ts) (key.subst ts) := by
  unfold namedOrigin originMatrix
  rw [blockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem namedOriginRename (b : Bool) (K m key : OTerm α) (j : α → β) :
    (namedOrigin b K m key).relabel j =
      namedOrigin b (K.relabel j) (m.relabel j) (key.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (namedOrigin b K m key).subst (fun a => emb (.var (j a))) = _
  rw [namedOriginSubst]
  simp only [← termRelabelAsSubst]

theorem introduce (b : Bool) (K m key ty i : OTerm α)
    (atWitness : Nonempty (Derivation body Γ
      (NumberedWindowInternalCoverNamedLeafOriginTargets.originRow b K m key ty i))) :
    Nonempty (Derivation body Γ (namedOrigin b K m key)) := by
  let ws : Fin 2 → OTerm α := ![ty,i]
  apply actualFiniteExistentialIntroduction body α 2 Γ _ (fun q => emb (ws q))
  have he : Sum.elim Term.var (fun q => emb (ws q)) = (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  rw [he]
  unfold originMatrix
  rw [rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  exact atWitness

/-- Eliminate the Cartesian binder without exposing a meta-language
numeral or substituting a different scratch/list report. -/
theorem cartesianCases {k : Nat} (D : Program (k+1)) (raw image : OTerm α)
    (params : Fin k → OTerm α) (goal : Formula α)
    (found : Nonempty (Derivation body Γ (hasOrigin D raw image params)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (source : OTerm β),
      (∀ r ∈ Γ, r.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (NumberedWindowInternalCoverCartesianFoldOriginTargets.originRow D (raw.relabel j) source (image.relabel j)
        (fun i => (params i).relabel j))) →
      Nonempty (Derivation body Δ (goal.relabel j))) :
    Nonempty (Derivation body Γ goal) := by
  obtain ⟨found⟩ := found
  unfold hasOrigin at found
  let A := originBinder D raw image params
  let Δ := A :: Γ.map weaken
  let j : α → α ⊕ Fin 1 := Sum.inl
  obtain ⟨done⟩ := next _ j Δ (.var (.inr 0))
    (fun r hr => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination found done⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafOriginBindingProof
