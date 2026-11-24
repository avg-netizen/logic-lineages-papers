module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (recRename programSubst consTermSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst conjunctionSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalOpenOriginScanRoutedHeadProof (loopRename)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedRowTargets (oneTerm Zero)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginScanInductionTargets

private theorem oneRename {α β : Type} (p : OTerm α) (f : α → β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → OTerm α) i).relabel f) = ![p.relabel f] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

private theorem oneSubst {α β : Type} (p : OTerm α) (f : α → OTerm β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → OTerm α) i).subst f) = ![p.subst f] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem filterRename {α β : Type} (side : Bool) (out rows pool : OTerm α) (j : α → β) :
    (filterGraph side out rows pool).relabel j =
      filterGraph side (out.relabel j) (rows.relabel j) (pool.relabel j) := by
  simp only [filterGraph,recRename,oneRename]

private theorem filterSubst {α β : Type} (side : Bool) (out rows pool : OTerm α) (f : α → OTerm β) :
    (filterGraph side out rows pool).subst (fun a => emb (f a)) =
      filterGraph side (out.subst f) (rows.subst f) (pool.subst f) := by
  simp only [filterGraph,recGraph,programSubst,consTermSubst,oneSubst]

private theorem loopSubst {α β : Type} (r : Program 3) (rows raw : OTerm α) (f : α → OTerm β) :
    (loopAccept r rows raw).subst (fun a => emb (f a)) = loopAccept r (rows.subst f) (raw.subst f) := by
  simp only [loopAccept,recGraph,programSubst,consTermSubst,oneSubst,oneTerm,sucSubst,zSubst,NumberedWindowInternalDirectInsertedRowTargets.Zero]

theorem goalRename {α β : Type} (r : Program 3) (l r' vl vr : OTerm α) (j : α → β) :
    (goalAt r l r' vl vr).relabel j =
      goalAt r (l.relabel j) (r'.relabel j) (vl.relabel j) (vr.relabel j) := by
  simp only [goalAt,conjunctionRename,loopRename]

theorem suppliedRename {α β : Type} (r : Program 3)
    (rows old l r' s vl vr : OTerm α) (j : α → β) :
    (suppliedAt r rows old l r' s vl vr).relabel j =
      suppliedAt r (rows.relabel j) (old.relabel j) (l.relabel j) (r'.relabel j)
        (s.relabel j) (vl.relabel j) (vr.relabel j) := by
  simp only [suppliedAt,impRename,conjunctionRename,loopRename,filterRename,goalRename]

private theorem suppliedSubst {α β : Type} (r : Program 3)
    (rows old l r' s vl vr : OTerm α) (f : α → OTerm β) :
    (suppliedAt r rows old l r' s vl vr).subst (fun a => emb (f a)) =
      suppliedAt r (rows.subst f) (old.subst f) (l.subst f) (r'.subst f)
        (s.subst f) (vl.subst f) (vr.subst f) := by
  simp only [suppliedAt,impSubst,conjunctionSubst,loopSubst,filterSubst,goalAt]

theorem matrixWitness {α : Type} (r : Program 3) (rows old l r' s vl vr : OTerm α) :
    (matrix r rows old l r' s).subst (Sum.elim Term.var (fun i => emb (![vl,vr] i))) =
      suppliedAt r rows old l r' s vl vr := by
  let witnesses : Fin 2 → OTerm α := ![vl,vr]
  have he : (Sum.elim Term.var (fun i => emb (witnesses i))) =
      (fun a => emb (Sum.elim Term.var witnesses a)) := by
    funext a
    cases a <;> rfl
  change (matrix r rows old l r' s).subst (Sum.elim Term.var (fun i => emb (witnesses i))) = _
  rw [he]
  simp only [matrix,suppliedSubst,witnessLift,Term.subst,Sum.elim_inr,witnesses] <;> rfl

theorem atRowsRename {α β : Type} (r : Program 3) (rows old l r' s : OTerm α) (j : α → β) :
    (atRows r rows old l r' s).relabel j =
      atRows r (rows.relabel j) (old.relabel j) (l.relabel j) (r'.relabel j) (s.relabel j) := by
  unfold atRows
  rw [allBlockRename]
  have he : ((Sum.map j id : α ⊕ Fin 2 → β ⊕ Fin 2) ∘ Sum.inl) = Sum.inl ∘ j := rfl
  simp only [matrix,suppliedRename,Term.relabel_relabel,he,Term.relabel] <;> rfl

private theorem atRowsSubst {α β : Type} (r : Program 3) (rows old l r' s : OTerm α)
    (f : α → OTerm β) :
    (atRows r rows old l r' s).subst (fun a => emb (f a)) =
      atRows r (rows.subst f) (old.subst f) (l.subst f) (r'.subst f) (s.subst f) := by
  unfold atRows
  rw [allBlockSubst,liftedEmbedding]
  simp only [matrix,suppliedSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem motiveAtCode {α : Type} (r : Program 3) (code old l r' s : OTerm α) :
    atCode (motive r old l r' s) code = atRows r code old l r' s := by
  unfold atCode
  unfold instantiate
  change (atRows r (.var (.inr (0 : Fin 1))) (old.relabel Sum.inl) (l.relabel Sum.inl)
      (r'.relabel Sum.inl) (s.relabel Sum.inl)).subst (Sum.elim Term.var (fun _ => emb code)) = _
  have eq : (Sum.elim Term.var (fun _ : Fin 1 => emb code)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => code) a)) := by
    funext a
    cases a <;> rfl
  rw [eq,atRowsSubst]
  simp only [witnessLift,Term.subst] <;> rfl

theorem motiveAtIndex {α : Type} (r : Program 3) (old l r' s : OTerm α) (i : Fin 3) :
    atIndex (motive r old l r' s) i =
      atRows r (.var (.inr i)) (old.relabel Sum.inl) (l.relabel Sum.inl)
        (r'.relabel Sum.inl) (s.relabel Sum.inl) := by
  unfold atIndex
  simp only [motive,atRowsRename,Term.relabel_relabel]
  rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem applyAtRows (r : Program 3) (rows old l r' s vl vr : OTerm α)
    (law : D B Γ (atRows r rows old l r' s))
    (allOld : D B Γ (loopAccept r rows old))
    (filterL : D B Γ (filterGraph true vl rows s))
    (filterR : D B Γ (filterGraph false vr rows s)) : D B Γ (goalAt r l r' vl vr) := by
  obtain ⟨h⟩ := actualFiniteUniversalElimination B α 2 Γ (matrix r rows old l r' s)
    (fun i => emb (![vl,vr] i)) law
  rw [matrixWitness] at h
  obtain ⟨a⟩ := allOld
  obtain ⟨l⟩ := filterL
  obtain ⟨r'⟩ := filterR
  exact ⟨Derivation.implicationElimination h
    (Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction l r'))⟩

theorem renamePools {β : Type} {Δ : List (Formula β)}
    {removed decoded rawL rawR scratchL scratchR joined : OTerm α}
    (p : Pools B Γ removed decoded rawL rawR scratchL scratchR joined) (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Pools B Δ (removed.relabel j) (decoded.relabel j) (rawL.relabel j) (rawR.relabel j)
      (scratchL.relabel j) (scratchR.relabel j) (joined.relabel j) := by
  refine ⟨renameParser removed decoded p.oldParsed j Δ keep,
    renameParser rawL scratchL p.leftParsed j Δ keep,
    renameParser rawR scratchR p.rightParsed j Δ keep, ?_, ?_⟩
  · simpa only [sucRelabel,zRelabel] using renamePair permutation (suc z) decoded joined p.count j keep
  · exact renamePair append joined scratchL scratchR p.appended j keep

#print axioms applyAtRows

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
