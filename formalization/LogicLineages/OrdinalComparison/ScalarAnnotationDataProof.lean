module
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataStructureProof
public import LogicLineages.OrdinalComparison.ScalarPartialActivityProof
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Proof
open ActiveScalarAnnotation AdditiveHeadTree AssignmentSupport SourceFreeOccurrences

theorem valid_one {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))} :
    Valid (Tree.free (k := k) (F := F) .one) :=
  ⟨GeneratedOrdinalGrade.one 0,by simp [Active]⟩

theorem free_ground_partial {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hd : Valid d)
    (hf : ordinalHeadFree (erase d) = true) :
    ∃ (out : Tree k Γ F) (v : OrdinalPartialVector Γ .ground),
      groundPartial d = some out ∧ AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (erase d) = some v ∧
      erase out = v 0 ∧ Valid out := by
  refine ⟨.add (closeTree d) (.free .one),ordinalFreePartialVector 0 (erase d),?_,?_,?_,?_⟩
  · rw [groundPartial.eq_def,if_pos hf]
  · rw [AdmissiblePartial.run.eq_def,if_pos hf]
  · change (.add (erase (closeTree d)) .one : OrdinalExpression Γ) = .add (ordinalHeadClosure (erase d)) .one
    rw [close_erase]
  · exact ⟨close_valid d hd,valid_one⟩

theorem exactGroundPartial : Targets.ExactGroundPartial := by
  intro k Γ F d
  induction d with
  | free q =>
    intro hd
    by_cases hf : ordinalHeadFree (erase (Tree.free (k := k) (F := .there F) q)) = true
    · exact free_ground_partial _ hd hf
    obtain ⟨v,hv,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ .ground
      OrdinalSyntax.defaultPolicy 0 q hd.1
    refine ⟨.free (v 0),v,?_,hv,rfl,?_,?_⟩
    · rw [groundPartial.eq_def,if_neg hf]
      simp only [hv,Option.map_some]
    · exact hg 0
    · intro ha
      have hm := AssignmentSupport.Proof.actualPartialSupport Γ .ground OrdinalSyntax.defaultPolicy 0 q v hv 0 _ ha
      exact hd.2 ((TrackedSource.Proof.mem_dropBound F (names q)).mp hm)
  | tracked =>
    intro hd
    exact free_ground_partial _ hd (by rfl)
  | add a b iha ihb =>
    intro hd
    by_cases hf : ordinalHeadFree (erase (.add a b)) = true
    · exact free_ground_partial _ hd hf
    obtain ⟨oa,va,hoa,hva,hea,hda⟩ := iha hd.1
    obtain ⟨ob,vb,hob,hvb,heb,hdb⟩ := ihb hd.2
    refine ⟨.add (.add oa ob) (.free .one),
      (fun j => AdmissiblePartial.three OrdinalSyntax.defaultPolicy .activeAdd (va j) (vb j) .one),
      ?_,?_,?_,?_⟩
    · rw [groundPartial.eq_def,if_neg hf]
      simp only [hoa,hob,Option.bind_some,pure]
      rfl
    · rw [AdmissiblePartial.run.eq_def,if_neg hf]
      simp only [erase,hva,hvb,Option.bind_some,pure]
      rfl
    · change (.add (.add (erase oa) (erase ob)) .one : OrdinalExpression Γ) = _
      rw [hea,heb]
      rfl
    · exact ⟨⟨hda,hdb⟩,valid_one⟩
  | collapse op tail ih =>
    intro hd
    by_cases hf : ordinalHeadFree (erase (.collapse op tail)) = true
    · exact free_ground_partial _ hd hf
    obtain ⟨out,pt,hout,hpt,het,hdt⟩ := ih hd.2.2.2
    have hheadfree : ordinalHeadFree op.head = true :=
      actualGeneratedHeadFreeAbove Γ .ground 1 op.head (AdditiveHeadTree.Proof.head_grade hd.2.1) (by decide)
    have hph : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 1 op.head =
        some (ordinalFreePartialVector 1 op.head) := by
      rw [AdmissiblePartial.run.eq_def,if_pos hheadfree]
    let v : OrdinalPartialVector Γ .ground := fun j => if j.val = 0 then
      .collapse (ordinalHeadClosure op.head) (pt 0)
      else .add (ordinalFreePartialVector 1 op.head j) (pt j)
    refine ⟨.collapse (closeOperator op) out,v,?_,?_,?_,?_⟩
    · rw [groundPartial.eq_def,if_neg hf]
      simp only [hout,Option.bind_some,pure]
      rfl
    · rw [AdmissiblePartial.run.eq_def,if_neg hf]
      simp only [erase,hph,hpt,if_pos rfl,Option.bind_some,pure]
      rfl
    · change (.collapse (ordinalHeadClosure op.head) (erase out) : OrdinalExpression Γ) = .collapse (ordinalHeadClosure op.head) (pt 0)
      rw [het]
    · refine ⟨closeOperator_assignment op hd.1,
        AdditiveHeadTree.Proof.headClosureHead k Γ F op.head hd.2.1,?_,hdt⟩
      intro hh
      have hhold : Active (.there F) op.head := (ActiveScalarAnnotation.Proof.active_headClosure F op.head).mp hh
      have htail := hd.2.2.1 hhold
      have hold := (TrackedSource.Proof.mem_dropBound F (names (erase tail))).mpr htail
      have hnew := (ScalarPartialActivity.Proof.exactScalarOldNames Γ .ground OrdinalSyntax.defaultPolicy
        (erase tail) pt hpt ⟨_,F⟩).mpr hold
      change (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ) ∈ names (erase out)
      rw [het]
      exact hnew
end LogicLineages.OrdinalComparison.Source.ScalarAnnotationData.Proof
