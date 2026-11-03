module
public import LogicLineages.OrdinalComparison.ActiveScalarAnnotationStructureProof
public import LogicLineages.OrdinalComparison.ScalarPartialActivityPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof
open SourceFreeOccurrences AssignmentSupport AssignmentSupport.Proof AdmissibleSum

private theorem free_partial_annotation {k Γ} (F : Variable Γ (Ty.curriedGround (k+1)))
    (p : Policy) (q : OrdinalExpression (.ground :: Γ)) (v : OrdinalPartialVector Γ .ground)
    (hq : Annotated p (.there F) q) (hf : ordinalHeadFree q = true)
    (hv : AdmissiblePartial.run p 0 q = some v) : Annotated p F (v 0) := by
  rw [AdmissiblePartial.run.eq_def, if_pos hf] at hv
  cases hv
  simp only [ordinalFreePartialVector, Fin.val_zero, ↓reduceIte]
  exact .add (headClosureTransport k Γ F p q hq) (.free (by simp [Active]))

theorem groundPartialTransport : Targets.GroundPartialTransport := by
  intro k Γ F p q v hq
  induction hq generalizing v with
  | @free q hn =>
    intro hv
    apply Annotated.free
    intro ha
    have hm := actualPartialSupport Γ .ground p 0 q v hv 0 _ ha
    exact hn ((TrackedSource.Proof.mem_dropBound F (names q)).mp hm)
  | tracked =>
    intro hv
    exact free_partial_annotation F p _ v .tracked (by rfl) hv
  | @add a b ha hb iha ihb =>
    intro hv
    by_cases hf : ordinalHeadFree (.add a b) = true
    · exact free_partial_annotation F p _ v (.add ha hb) hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hpa : AdmissiblePartial.run p 0 a with
      | none => simp [hpa] at hv
      | some pa =>
        cases hpb : AdmissiblePartial.run p 0 b with
        | none => simp [hpa, hpb] at hv
        | some pb =>
          simp [hpa, hpb] at hv
          subst v
          unfold AdmissiblePartial.three
          apply annotated_expand
          intro j
          split_ifs
          · exact iha pa hpa
          · exact ihb pb hpb
          · exact .free (by simp [Active])
  | @collapse h t op hs ht ih =>
    intro hv
    by_cases hf : ordinalHeadFree (.collapse h t) = true
    · exact free_partial_annotation F p _ v (.collapse op hs ht) hf hv
    · rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
      dsimp only at hv
      cases hph : AdmissiblePartial.run p 1 h with
      | none => simp [hph] at hv
      | some ph =>
        cases hpt : AdmissiblePartial.run p 0 t with
        | none => simp [hph, hpt] at hv
        | some pt =>
          simp [hph, hpt] at hv
          subst v
          simp only [Fin.val_zero, ↓reduceIte]
          refine .collapse (GroundOperatorDischarge.Proof.operatorWitnessTransport Γ p h op) ?_ (ih pt hpt)
          intro hh
          have htail := hs ((active_headClosure F h).mp hh)
          have hold := (TrackedSource.Proof.mem_dropBound F (names t)).mpr htail
          exact (ScalarPartialActivity.Proof.exactScalarOldNames Γ .ground p t pt hpt _).mpr hold

end LogicLineages.OrdinalComparison.Source.ActiveScalarAnnotation.Proof
