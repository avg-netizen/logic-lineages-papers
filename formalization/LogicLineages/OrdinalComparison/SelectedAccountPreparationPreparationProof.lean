module
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationRenamingProof
public import LogicLineages.OrdinalComparison.WWSelectedBinderProof
public import LogicLineages.OrdinalComparison.WWSourceRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem selected_injective (left right : List Ty) (σ τ : Ty) :
    Function.Injective (fun x : Variable (left ++ σ :: right) τ => SelectedBinder.moveToHead left right σ x) := by
  intro x y he
  exact (SelectedBinder.Proof.from_to left right σ τ x).symm.trans
    ((congrArg (fun z => SelectedBinder.moveFromHead left right σ z) he).trans
      (SelectedBinder.Proof.from_to left right σ τ y))

theorem selectedCertificates : Targets.SelectedCertificates := by
  intro k left right p q
  have hc := certificateRenaming k (left ++ Ty.curriedGround (k+1) :: right)
    (Ty.curriedGround (k+1) :: (left ++ right))
    (SelectedBinder.moveToHead left right (Ty.curriedGround (k+1)))
    (selected_injective left right (Ty.curriedGround (k+1)))
    (SelectedBinder.selected left right (Ty.curriedGround (k+1))) p q
  simpa only [prepare,SelectedBinder.Proof.to_selected] using hc

theorem expression_rename_comp {Γ Δ Ξ : List Ty} (r : Renaming Γ Δ) (s : Renaming Δ Ξ)
    (q : OrdinalExpression Γ) :
    ordinalExpressionRename s (ordinalExpressionRename r q) =
      ordinalExpressionRename (fun x => s (r x)) q := by
  induction q with
  | var c => rcases c with ⟨τ,x,j⟩; rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [ordinalExpressionRename,substitute] at iha ihb ⊢
    rw [iha,ihb]

theorem groundPrefixStep : Targets.GroundPrefixStep := by
  intro left right σ q
  constructor
  · change ordinalExpressionRename
      (fun x => SelectedBinder.swap (Renaming.lift (SelectedBinder.moveToHead left right σ) x)) q = _
    exact (expression_rename_comp (Renaming.lift (SelectedBinder.moveToHead left right σ))
      (@SelectedBinder.swap (left ++ right) Ty.ground σ) q).symm
  · intro p i
    exact SourceRenaming.Proof.partialNaturality (left ++ σ :: right) (σ :: (left ++ right))
      Ty.ground (SelectedBinder.moveToHead left right σ) p i q
end LogicLineages.OrdinalComparison.Source.SelectedAccountPreparation.Proof
