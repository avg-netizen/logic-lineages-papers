module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportStructureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
open ActiveScalarAnnotation AdditiveHeadTree ScalarCarrierAccounting AssignmentSupport AssignmentSupport.Proof

theorem adjacent_partial_account_of_run {k Γ}
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q) :
    ∀ (xs : List Carrier) (c : Nat),
      Annotated OrdinalSyntax.defaultPolicy (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q →
      Account (before k [] Γ q) xs c →
      ∀ v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground,
        AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v →
        ∃ c' : Nat, Account (v 0) xs c' ∧ c ≤ c' := by
  induction ht with
  | @free q hg hn =>
    intro xs c ha hac v hv
    exact inactive_transport k Γ q xs c v hn hac hv
  | tracked =>
    intro xs c ha hac v hv
    exact ground_free_transport k Γ _ xs c v hac (by rfl) hv
  | @add a b ha hb iha ihb =>
    intro xs c hann hac v hv
    by_cases hn : ¬ Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (.add a b)
    · exact inactive_transport k Γ _ xs c v hn hac hv
    · have hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (.add a b) :=
        Classical.byContradiction hn
      by_cases hf : ordinalHeadFree (.add a b) = true
      · exact ground_free_transport k Γ _ xs c v hac hf hv
      · cases hann with
        | free hn => exact False.elim (hn hactive)
        | add hanna hannb =>
          rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
          dsimp only at hv
          cases hva : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 a with
          | none => simp [hva] at hv
          | some va =>
            cases hvb : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 b with
            | none => simp [hva,hvb] at hv
            | some vb =>
              simp [hva,hvb] at hv
              subst v
              change Account (.add (before k [] Γ a) (before k [] Γ b)) xs c at hac
              cases hac with
              | free hn => exact False.elim (hn ((before_active k Γ _).mpr hactive))
              | @add _ _ xs ys ca cb active aca acb =>
                obtain ⟨ca',aca',hlea⟩ := iha xs ca hanna aca va hva
                obtain ⟨cb',acb',hleb⟩ := ihb ys cb hannb acb vb hvb
                have hinner : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add (va 0) (vb 0)) := by
                  have hparts : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) a ∨
                      Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) b := by
                    simpa only [Active,names_add,List.mem_append] using hactive
                  change _ ∈ names (.add (va 0) (vb 0))
                  rw [names_add,List.mem_append]
                  rcases hparts with hpa | hpb
                  · exact Or.inl ((partial_active k Γ a va hva).mpr hpa)
                  · exact Or.inr ((partial_active k Γ b vb hvb).mpr hpb)
                have houter : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
                    (.add (.add (va 0) (vb 0)) .one) := by
                  simpa only [Active,names_add,names_one,List.append_nil] using hinner
                refine ⟨ca'+cb'+1+1+1,?_,by omega⟩
                have hinneracc : Account (.add (va 0) (vb 0)) (xs++ys) (ca'+cb'+1) :=
                  .add hinner aca' acb'
                have hone : Account (.one : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) [] 1 :=
                  .free (by simp [Active])
                have hout := Account.add houter hinneracc hone
                simpa [AdmissiblePartial.three, OrdinalSyntax.defaultPolicy, OrdinalSyntax.defaultShape,
                  OrdinalSyntax.leftShape, AdmissibleSum.expand] using hout
  | @collapse h t hh ht ih =>
    intro xs c hann hac v hv
    by_cases hn : ¬ Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (.collapse h t)
    · exact inactive_transport k Γ _ xs c v hn hac hv
    · have hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (.collapse h t) :=
        Classical.byContradiction hn
      by_cases hf : ordinalHeadFree (.collapse h t) = true
      · exact ground_free_transport k Γ _ xs c v hac hf hv
      · cases hann with
        | free hn => exact False.elim (hn hactive)
        | collapse op support hant =>
          have htail : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) t := by
            have hparts : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) h ∨
                Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) t := by
              simpa only [Active,names_collapse,List.mem_append] using hactive
            exact hparts.elim support id
          rw [AdmissiblePartial.run.eq_def, if_neg hf] at hv
          dsimp only at hv
          cases hvh : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 1 h with
          | none => simp [hvh] at hv
          | some vh =>
            cases hvt : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t with
            | none => simp [hvh,hvt] at hv
            | some vt =>
              simp [hvh,hvt] at hv
              subst v
              have houtactive : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
                  (.collapse (ordinalHeadClosure h) (vt 0)) := by
                change _ ∈ names (.collapse (ordinalHeadClosure h) (vt 0))
                rw [names_collapse,List.mem_append]
                exact Or.inr ((partial_active k Γ t vt hvt).mpr htail)
              have hcal := adjacentClosureCalibration k Γ h
              change Account (.collapse (before k [] Γ h) (before k [] Γ t)) xs c at hac
              cases hac with
              | free hn => exact False.elim (hn ((before_active k Γ _).mpr hactive))
              | @finite _ _ xs ct n active hfinite act =>
                obtain ⟨ct',act',hle⟩ := ih xs ct hant act vt hvt
                refine ⟨ct'+n+HeadFiniteSurplus.surplus (before k [] Γ h),?_,by omega⟩
                have hacc : Account (.collapse (ordinalHeadClosure h) (vt 0)) xs
                    (ct'+n+HeadFiniteSurplus.surplus (ordinalHeadClosure h)) :=
                  .finite houtactive (hcal.2.2.2.trans hfinite) act'
                simpa only [Fin.val_zero,↓reduceIte,hcal.2.2.1] using hacc
              | @nonfinite _ _ xs ct label active hnonfinite hlabel act =>
                obtain ⟨ct',act',hle⟩ := ih xs ct hant act vt hvt
                refine ⟨ct'+HeadFiniteSurplus.surplus (before k [] Γ h),?_,by omega⟩
                have hacc : Account (.collapse (ordinalHeadClosure h) (vt 0)) (xs++[label])
                    (ct'+HeadFiniteSurplus.surplus (ordinalHeadClosure h)) :=
                  .nonfinite label houtactive (hcal.2.2.2.symm ▸ hnonfinite)
                    (hlabel.trans hcal.2.2.2.symm) act'
                simpa only [Fin.val_zero,↓reduceIte,hcal.2.2.1] using hacc

theorem adjacent_partial_account {k Γ}
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List Carrier) (c : Nat)
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (ha : Annotated OrdinalSyntax.defaultPolicy (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (hac : Account (before k [] Γ q) xs c) :
    ∃ (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground) (c' : Nat),
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v ∧ Account (v 0) xs c' ∧ c ≤ c' := by
  obtain ⟨v,hv,hg⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated
    (Ty.curriedGround (k+1) :: Γ) .ground OrdinalSyntax.defaultPolicy 0 q
    (AdditiveHeadTree.Proof.scalar_grade ht)
  obtain ⟨c',hc',hle⟩ := adjacent_partial_account_of_run q ht xs c ha hac v hv
  exact ⟨v,c',hv,hc',hle⟩

end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
