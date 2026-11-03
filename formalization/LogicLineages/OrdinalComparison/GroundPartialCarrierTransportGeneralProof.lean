module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportAdjacentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
open ActiveScalarAnnotation AdditiveHeadTree ScalarCarrierAccounting

theorem lifted_selected_injective (left right : List Ty) (σ τ : Ty) :
    Function.Injective (fun x : Variable (Ty.ground :: (left ++ σ :: right)) τ =>
      Renaming.lift (SelectedBinder.moveToHead left right σ) x) := by
  intro x y he
  have hi : ∀ {υ} (z : Variable (left ++ σ :: right) υ),
      SelectedBinder.moveFromHead left right σ (SelectedBinder.moveToHead left right σ z) = z := by
    intro υ z
    exact SelectedBinder.Proof.from_to left right σ υ z
  have hx := SelectedBinder.Proof.lift_inverse (SelectedBinder.moveToHead left right σ)
    (SelectedBinder.moveFromHead left right σ) hi x
  have hy := SelectedBinder.Proof.lift_inverse (SelectedBinder.moveToHead left right σ)
    (SelectedBinder.moveFromHead left right σ) hi y
  exact hx.symm.trans ((congrArg (fun z => Renaming.lift (SelectedBinder.moveFromHead left right σ) z) he).trans hy)

theorem groundPartialAccount : Targets.GroundPartialAccount := by
  intro k left right q xs c ht ha haccount
  let r : Renaming (left ++ Ty.curriedGround (k+1) :: right)
      (Ty.curriedGround (k+1) :: (left ++ right)) :=
    SelectedBinder.moveToHead left right (Ty.curriedGround (k+1))
  let q' := ordinalExpressionRename (Renaming.lift r) q
  obtain ⟨v,hv,hvg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated
    (left ++ Ty.curriedGround (k+1) :: right) Ty.ground OrdinalSyntax.defaultPolicy 0 q
    (AdditiveHeadTree.Proof.scalar_grade ht)
  have hc := SelectedAccountPreparation.Proof.certificateRenaming k
    ((Ty.ground :: left) ++ Ty.curriedGround (k+1) :: right)
    (Ty.ground :: Ty.curriedGround (k+1) :: (left ++ right)) (Renaming.lift r)
    (lifted_selected_injective left right (Ty.curriedGround (k+1)))
    (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1))) OrdinalSyntax.defaultPolicy q
  have hF : Renaming.lift r (SelectedBinder.selected (Ty.ground :: left) right (Ty.curriedGround (k+1))) =
      .there (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _) := by
    change Variable.there (SelectedBinder.moveToHead left right (Ty.curriedGround (k+1))
      (SelectedBinder.selected left right (Ty.curriedGround (k+1)))) = Variable.there Variable.here
    rw [SelectedBinder.Proof.to_selected]
  rw [hF] at hc
  have ht' : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _)) q' := hc.2.1 ht
  have ha' : Annotated OrdinalSyntax.defaultPolicy
      (.there (.here : Variable (Ty.curriedGround (k+1) :: (left ++ right)) _)) q' := hc.2.2 ha
  have haccount' : Account (before k [] (left ++ right) q') xs c := by
    rw [before_adj_eq_swap]
    change Account (ordinalExpressionRename (@SelectedBinder.swap (left ++ right) Ty.ground (Ty.curriedGround (k+1)))
      (ordinalExpressionRename (Renaming.lift (SelectedBinder.moveToHead left right (Ty.curriedGround (k+1)))) q)) xs c
    rw [← (SelectedAccountPreparation.Proof.groundPrefixStep left right (Ty.curriedGround (k+1)) q).1]
    exact haccount
  obtain ⟨v',c',hv',hnew,hcc⟩ := adjacent_partial_account q' xs c ht' ha' haccount'
  have hn := SourceRenaming.Proof.partialNaturality (left ++ Ty.curriedGround (k+1) :: right)
    (Ty.curriedGround (k+1) :: (left ++ right)) Ty.ground r OrdinalSyntax.defaultPolicy 0 q
  rw [hv] at hn
  change AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q' = some (SourceRenaming.renamePartial r v) at hn
  have he : v' = SourceRenaming.renamePartial r v := Option.some.inj (hv'.symm.trans hn)
  subst v'
  refine ⟨v,c',hv,hnew,hcc,?_⟩
  have hi : (c : Int) ≤ (c' : Int) := by exact_mod_cast hcc
  unfold reserve
  omega
end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
