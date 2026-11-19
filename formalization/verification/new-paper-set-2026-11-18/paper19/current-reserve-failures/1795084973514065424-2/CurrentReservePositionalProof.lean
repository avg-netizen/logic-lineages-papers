module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveAdjacentProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus AdmissibleSum
open CurrentUnaryChain (commonUnits)
open SelectedAccountPreparation.Proof (selectedCertificates selected_injective groundPrefixStep)

theorem liftedSelectedInjective (left right : List Ty) (σ τ : Ty) :
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

theorem groundPartialAccountTransport : CurrentReserveTargets.GroundPartialAccountTransport := by
  intro p f k left right q xs c ht ha hAccount
  let σ := Ty.curriedGround (k+1)
  let r : Renaming (left ++ σ :: right) (σ :: (left ++ right)) :=
    SelectedBinder.moveToHead left right σ
  let q' := ordinalExpressionRename (Renaming.lift r) q
  obtain ⟨v,hv,_⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated
    (left ++ σ :: right) .ground p 0 q (AdditiveHeadTree.Proof.scalar_grade ht)
  have hc := SelectedAccountPreparation.Proof.certificateRenaming k
    ((.ground :: left) ++ σ :: right) (.ground :: σ :: (left ++ right))
    (Renaming.lift r) (liftedSelectedInjective left right σ)
    (SelectedBinder.selected (.ground :: left) right σ) p q
  have hF : Renaming.lift r (SelectedBinder.selected (.ground :: left) right σ) =
      .there (.here : Variable (σ :: (left ++ right)) σ) := by
    change Variable.there (SelectedBinder.moveToHead left right σ
      (SelectedBinder.selected left right σ)) = Variable.there Variable.here
    rw [SelectedBinder.Proof.to_selected]
  rw [hF] at hc
  have ht' : ScalarTrees (.there (.here : Variable (σ :: (left ++ right)) σ)) q' := hc.2.1 ht
  have ha' : Annotated p (.there (.here : Variable (σ :: (left ++ right)) σ)) q' := hc.2.2 ha
  have hAccount' : Account p f (before k [] (left ++ right) q') xs c := by
    rw [beforeAdjEqSwap]
    change Account p f (ordinalExpressionRename (@SelectedBinder.swap (left ++ right) .ground σ)
      (ordinalExpressionRename (Renaming.lift (SelectedBinder.moveToHead left right σ)) q)) xs c
    rw [← (groundPrefixStep left right σ q).1]
    exact hAccount
  obtain ⟨v',c',hv',hnew,hcc⟩ := adjacentAccount p f q' xs c ht' ha' hAccount'
  have hn := SourceRenaming.Proof.partialNaturality (left ++ σ :: right)
    (σ :: (left ++ right)) .ground r p 0 q
  rw [hv] at hn
  change AdmissiblePartial.run p 0 q' = some (SourceRenaming.renamePartial r v) at hn
  have he : v' = SourceRenaming.renamePartial r v := Option.some.inj (hv'.symm.trans hn)
  subst v'
  exact ⟨v,c',hv,hnew,hcc,reserveMonotone hcc⟩

theorem preparedAssignment (p : Policy) {σ τ : Ty} (left right : List Ty)
    (a : OriginalTerm (left ++ σ :: right) τ)
    (u : OrdinalVector (left ++ σ :: right) τ.level)
    (hu : AdmissibleAssignment.assignment p a = some u) :
    AdmissibleAssignment.assignment p (SelectedAccountPreparation.prepareSource left right σ a) =
      some (SourceRenaming.renameVector (SelectedBinder.moveToHead left right σ) u) := by
  rw [SelectedAccountPreparation.prepareSource,SourceRenaming.Proof.assignmentNaturality,hu]
  rfl

theorem actualGroundPartialTransport : CurrentReserveTargets.ActualGroundPartialTransport := by
  intro p f k left right n e
  let σ := Ty.curriedGround (k+1)
  let F := SelectedBinder.selected (.ground :: left) right σ
  obtain ⟨u,hu,ht,ha⟩ := originalCertificates p k ((.ground :: left) ++ σ :: right) F n e
  have hsel := selectedCertificates k (.ground :: left) right p (u 0)
  have htrees : ScalarTrees (.here : Variable (σ :: (.ground :: left) ++ right) σ)
    (before k left right (u 0)) := hsel.2.1 ht
  have hAnn : Annotated p (.here : Variable (σ :: (.ground :: left) ++ right) σ)
    (before k left right (u 0)) := hsel.2.2 ha
  obtain ⟨xs,c,oldPart,hOrigin,hOldAcc,hOldRun,hOld⟩ := exactAnnotatedAccounting p f k
    ((.ground :: left) ++ right) (before k left right (u 0)) htrees hAnn
  obtain ⟨v,c',hv,hnew,hcc,hres⟩ := groundPartialAccountTransport p f k left right
    (u 0) xs c ht ha hOldAcc
  have hvtrees := AdditiveHeadTree.StatementChecks.ground_partial_trees k
    (left ++ σ :: right) (SelectedBinder.selected left right σ) p (u 0) v ht hv
  have hafter := (selectedCertificates k left right p (v 0)).2.1 hvtrees.1
  obtain ⟨newPart,hNewRun,hNew⟩ := exactAccountValue p f k (left ++ right)
    (after k left right (v 0)) xs c' hafter hnew
  refine ⟨u,xs,c,v,c',oldPart,newPart,hu,preparedAssignment p (.ground :: left) right _ u hu,
    hOrigin,hOldAcc,hv,hnew,hcc,hres,hOldRun,hNewRun,?_⟩
  intro μ ν
  exact ⟨hOld μ,hNew ν⟩

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
