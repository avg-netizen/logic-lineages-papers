module
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationTargets
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
public import LogicLineages.OrdinalComparison.WWGeneratedGradeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof
open SourceFreeOccurrences AssignmentSupport AssignmentSupport.Proof ActiveScalarAnnotation AdditiveHeadTree
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem names_rename {Γ Δ} (r : Renaming Γ Δ) (q : OrdinalExpression Γ) :
    names (ordinalExpressionRename r q) = (names q).map (renamePacked r) := by
  induction q with
  | var c => rcases c with ⟨τ,x,j⟩; rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalExpressionRename, substitute] at iha ihb ⊢
    simp only [names_add, names_emul, names_collapse, iha, ihb, List.map_append]

theorem renamePacked_injective {Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x)) :
    Function.Injective (renamePacked r) := by
  intro a b he
  rcases a with ⟨τ,x⟩
  rcases b with ⟨υ,y⟩
  have ht : τ = υ := congrArg Sigma.fst he
  cases ht
  have hv : r x = r y := by
    simpa only [renamePacked, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  exact congrArg (Sigma.mk τ) (hinj τ hv)

theorem active_rename {k Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x))
    (F : Variable Γ (Ty.curriedGround (k+1))) (q : OrdinalExpression Γ) :
    Active (r F) (ordinalExpressionRename r q) ↔ Active F q := by
  unfold Active
  rw [names_rename]
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
    have he' : y = (⟨_,F⟩ : PackedVariable Γ) := renamePacked_injective r hinj he
    simpa only [he'] using hy
  · intro hx
    exact List.mem_map.mpr ⟨⟨_,F⟩,hx,rfl⟩

theorem operator_rename {Γ Δ} (r : Renaming Γ Δ) (p : AdmissibleSum.Policy)
    (h : OrdinalExpression Γ) (hop : GroundOperatorDischarge.OperatorWitness p h) :
    GroundOperatorDischarge.OperatorWitness p (ordinalExpressionRename r h) := by
  obtain ⟨n,t,u,hu,hh⟩ := hop
  refine ⟨n,t.rename r,SourceRenaming.renameVector r u,?_,?_⟩
  · rw [SourceRenaming.Proof.assignmentNaturality,hu]
    rfl
  · exact congrArg (ordinalExpressionRename r) hh

theorem head_rename {k Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x))
    (F : Variable Γ (Ty.curriedGround (k+1))) {q : OrdinalExpression Γ}
    (hq : HeadTree F q) : HeadTree (r F) (ordinalExpressionRename r q) := by
  induction hq with
  | free hg hn =>
    exact .free (actualGeneratedGradeRenaming Γ Δ r 1 _ hg)
      (fun ha => hn ((active_rename r hinj F _).mp ha))
  | tracked => exact .tracked
  | add _ _ iha ihb => exact .add iha ihb

theorem scalar_rename {k Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x))
    (F : Variable Γ (Ty.curriedGround (k+1))) {q : OrdinalExpression Γ}
    (hq : ScalarTrees F q) : ScalarTrees (r F) (ordinalExpressionRename r q) := by
  induction hq with
  | free hg hn =>
    exact .free (actualGeneratedGradeRenaming Γ Δ r 0 _ hg)
      (fun ha => hn ((active_rename r hinj F _).mp ha))
  | tracked => exact .tracked
  | add _ _ iha ihb => exact .add iha ihb
  | collapse hh _ ih => exact .collapse (head_rename r hinj F hh) ih

theorem annotation_rename {k Γ Δ} (r : Renaming Γ Δ)
    (hinj : ∀ τ : Ty, Function.Injective (fun x : Variable Γ τ => r x))
    (F : Variable Γ (Ty.curriedGround (k+1))) (p : AdmissibleSum.Policy)
    {q : OrdinalExpression Γ} (hq : Annotated p F q) :
    Annotated p (r F) (ordinalExpressionRename r q) := by
  induction hq with
  | free hn => exact .free (fun ha => hn ((active_rename r hinj F _).mp ha))
  | tracked => exact .tracked
  | add _ _ iha ihb => exact .add iha ihb
  | collapse op hs _ ih =>
    exact .collapse (operator_rename r p _ op)
      (fun ha => (active_rename r hinj F _).mpr (hs ((active_rename r hinj F _).mp ha))) ih

theorem certificateRenaming : Targets.CertificateRenaming := by
  intro k Γ Δ r hinj F p q
  exact ⟨head_rename r hinj F, scalar_rename r hinj F, annotation_rename r hinj F p⟩

end LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof
