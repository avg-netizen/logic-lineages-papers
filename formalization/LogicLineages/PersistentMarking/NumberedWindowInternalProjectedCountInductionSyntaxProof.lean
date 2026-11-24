module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst consTermSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst conjunctionSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOriginScanInductionSyntaxProof (filterRename)
open NumberedWindowInternalProjectedCountLeftTargets (D)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalProjectedCountInductionTargets

private theorem oneSubst {α β : Type} (p : OTerm α) (f : α → OTerm β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → OTerm α) i).subst f) = ![p.subst f] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

private theorem twoSubst {α β : Type} (x y : OTerm α) (f : α → OTerm β) :
    (fun i : Fin 2 => ((![x,y] : Fin 2 → OTerm α) i).subst f) = ![x.subst f,y.subst f] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem filterSubst {α β : Type} (side : Bool) (out rows pool : OTerm α) (f : α → OTerm β) :
    (filterGraph side out rows pool).subst (fun a => emb (f a)) =
      filterGraph side (out.subst f) (rows.subst f) (pool.subst f) := by
  simp only [filterGraph,recGraph,programSubst,consTermSubst,oneSubst]

theorem projectRename {α β : Type} (out code : OTerm α) (j : α → β) :
    (project out code).relabel j = project (out.relabel j) (code.relabel j) := by
  simp only [project,unaryRename,sucRelabel]

theorem comparedRename {α β : Type} (p a : OTerm α) (j : α → β) :
    (compared p a).relabel j = compared (p.relabel j) (a.relabel j) := by
  simp only [compared,observer,programRename,binaryInputsRename,sucRelabel,zRelabel]

theorem appendedRename {α β : Type} (a l r : OTerm α) (j : α → β) :
    (appendGraph a l r).relabel j = appendGraph (a.relabel j) (l.relabel j) (r.relabel j) := by
  simp only [appendGraph,programRename,binaryInputsRename]

theorem matrixReportRename {α β : Type} (code pool vl vr p pl pr a : OTerm α) (j : α → β) :
    (reportMatrix code pool vl vr p pl pr a).relabel j =
      reportMatrix (code.relabel j) (pool.relabel j) (vl.relabel j) (vr.relabel j)
        (p.relabel j) (pl.relabel j) (pr.relabel j) (a.relabel j) := by
  simp only [reportMatrix,conjunctionRename,filterRename,projectRename,appendedRename]

private theorem matrixReportSubst {α β : Type} (code pool vl vr p pl pr a : OTerm α) (f : α → OTerm β) :
    (reportMatrix code pool vl vr p pl pr a).subst (fun x => emb (f x)) =
      reportMatrix (code.subst f) (pool.subst f) (vl.subst f) (vr.subst f)
        (p.subst f) (pl.subst f) (pr.subst f) (a.subst f) := by
  simp only [reportMatrix,conjunctionSubst,filterSubst,project,appendGraph,unary,
    programSubst,oneSubst,twoSubst,sucSubst]

private theorem consequentSubst {α β : Type} (code pool vl vr p pl pr a : OTerm α) (f : α → OTerm β) :
    (consequent code pool vl vr p pl pr a).subst (fun x => emb (f x)) =
      consequent (code.subst f) (pool.subst f) (vl.subst f) (vr.subst f)
        (p.subst f) (pl.subst f) (pr.subst f) (a.subst f) := by
  simp only [consequent,impSubst,matrixReportSubst,compared,observer,programSubst,twoSubst,sucSubst,zSubst]

private theorem consequentRename {α β : Type} (code pool vl vr p pl pr a : OTerm α) (j : α → β) :
    (consequent code pool vl vr p pl pr a).relabel j =
      consequent (code.relabel j) (pool.relabel j) (vl.relabel j) (vr.relabel j)
        (p.relabel j) (pl.relabel j) (pr.relabel j) (a.relabel j) := by
  simp only [consequent,impRename,matrixReportRename,comparedRename]

private theorem witnesses {α : Type} (code pool vl vr p pl pr a : OTerm α) :
    (matrix code pool).subst (Sum.elim Term.var (fun i => emb (![vl,vr,p,pl,pr,a] i))) =
      consequent code pool vl vr p pl pr a := by
  let ws : Fin 6 → OTerm α := ![vl,vr,p,pl,pr,a]
  have he : (Sum.elim Term.var (fun i => emb (ws i))) =
      (fun x => emb (Sum.elim Term.var ws x)) := by
    funext x
    cases x <;> rfl
  change (matrix code pool).subst (Sum.elim Term.var (fun i => emb (ws i))) = _
  rw [he]
  simp only [matrix,consequentSubst,witnessLift,Term.subst,Sum.elim_inr,ws] <;> rfl

theorem atRowsRename {α β : Type} (code pool : OTerm α) (j : α → β) :
    (atRows code pool).relabel j = atRows (code.relabel j) (pool.relabel j) := by
  unfold atRows
  rw [allBlockRename]
  have h : ((Sum.map j id : α ⊕ Fin 6 → β ⊕ Fin 6) ∘ Sum.inl) = Sum.inl ∘ j := rfl
  simp only [matrix,consequentRename,Term.relabel_relabel,h,Term.relabel] <;> rfl

private theorem atRowsSubst {α β : Type} (code pool : OTerm α) (f : α → OTerm β) :
    (atRows code pool).subst (fun x => emb (f x)) = atRows (code.subst f) (pool.subst f) := by
  unfold atRows
  rw [allBlockSubst,liftedEmbedding]
  simp only [matrix,consequentSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem motiveAtCode {α : Type} (code pool : OTerm α) :
    atCode (motive pool) code = atRows code pool := by
  unfold atCode instantiate
  change (atRows (.var (.inr (0 : Fin 1))) (pool.relabel Sum.inl)).subst
    (Sum.elim Term.var (fun _ => emb code)) = _
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb code)) =
      (fun x => emb (Sum.elim Term.var (fun _ : Fin 1 => code) x)) := by
    funext x
    cases x <;> rfl
  rw [he,atRowsSubst]
  simp only [witnessLift,Term.subst] <;> rfl

theorem motiveAtIndex {α : Type} (pool : OTerm α) (i : Fin 3) :
    atIndex (motive pool) i = atRows (.var (.inr i)) (pool.relabel Sum.inl) := by
  unfold atIndex
  simp only [motive,atRowsRename,Term.relabel_relabel]
  rfl

theorem applyAtRows {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (code pool vl vr p pl pr a : OTerm α) (law : D B Γ (atRows code pool))
    (report : D B Γ (reportMatrix code pool vl vr p pl pr a)) :
    D B Γ (compared p a) := by
  obtain ⟨d⟩ := actualFiniteUniversalElimination B α 6 Γ (matrix code pool)
    (fun i => emb (![vl,vr,p,pl,pr,a] i)) law
  rw [witnesses] at d
  obtain ⟨h⟩ := report
  exact ⟨Derivation.implicationElimination d h⟩

#print axioms applyAtRows
end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionSyntaxProof
