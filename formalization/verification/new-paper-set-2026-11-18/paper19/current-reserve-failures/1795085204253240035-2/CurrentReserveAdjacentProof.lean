module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveGroundUnitProof
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveTernaryProof
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationPreparationProof
public import LogicLineages.OrdinalComparison.ScalarPartialActivityPartialProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation AdditiveHeadTree AssignmentSupport AdmissibleSum SourceFreeOccurrences
open HeadFiniteSurplus

theorem beforeAdjEqSwap (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ)) :
    before k [] Γ q = ordinalExpressionRename
      (@SelectedBinder.swap Γ Ty.ground (Ty.curriedGround (k+1))) q := by
  induction q with
  | var c => rcases c with ⟨τ,x,j⟩; cases x with
    | here => rfl
    | there x => cases x <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [before,SelectedAccountPreparation.prepare,ordinalExpressionRename,substitute] at iha ihb ⊢
    rw [iha,ihb]
    rfl

theorem beforeActive (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ)) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Ty.ground :: Γ) _) (before k [] Γ q) ↔
      Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q := by
  have ha := SelectedAccountPreparation.Proof.active_rename
    (SelectedBinder.moveToHead [Ty.ground] Γ (Ty.curriedGround (k+1)))
    (SelectedAccountPreparation.Proof.selected_injective [Ty.ground] Γ (Ty.curriedGround (k+1)))
    (SelectedBinder.selected [Ty.ground] Γ (Ty.curriedGround (k+1))) q
  rw [SelectedBinder.Proof.to_selected] at ha
  exact ha

private theorem adjacentClose (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ)) :
    GroundClosing.expression (GroundClosing.GroundMap.lift (GroundOperatorDischarge.groundMap Γ))
      (before k [] Γ q) = ordinalHeadClosure q := by
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => rfl
    | there x => cases x <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [before,SelectedAccountPreparation.prepare,ordinalExpressionRename,
      GroundClosing.expression,ordinalHeadClosure,substitute] at iha ihb ⊢
    rw [iha,ihb]

theorem adjacentCloseAccount (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List (Carrier p)) (c : Nat) (ha : Account p f (before k [] Γ q) xs c) :
    Account p f (ordinalHeadClosure q) xs c := by
  have h := groundUnitAccountTransport p f k (.ground :: Γ) Γ
    (GroundOperatorDischarge.groundMap Γ) (before k [] Γ q) xs c ha
  rw [adjacentClose k Γ q] at h
  exact h

private theorem adjacentHeadMap (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (h : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ)) :
    unitValue f (ordinalHeadClosure h) = unitValue f (before k [] Γ h) := by
  rw [← adjacentClose k Γ h]
  exact exactUnitMap f _ _

private theorem adjacentSurplus (k : Nat) (Γ : List Ty)
    (h : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ)) :
    surplus (ordinalHeadClosure h) = surplus (before k [] Γ h) := by
  rw [← adjacentClose k Γ h]
  exact surplusMap (GroundOperatorDischarge.groundMap Γ) _

theorem partialActive (p : Policy) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground)
    (hv : AdmissiblePartial.run p 0 q = some v) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (v 0) ↔
      Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q := by
  change (⟨Ty.curriedGround (k+1),Variable.here⟩ : PackedVariable (Ty.curriedGround (k+1) :: Γ)) ∈ names (v 0) ↔ _
  exact (ScalarPartialActivity.Proof.exactScalarOldNames (Ty.curriedGround (k+1) :: Γ)
    .ground p q v hv ⟨_,.here⟩).trans
    (TrackedSource.Proof.mem_dropBound (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (names q))

private theorem inactiveTransport (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List (Carrier p)) (c : Nat)
    (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground)
    (hn : ¬ Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (ha : Account p f (before k [] Γ q) xs c)
    (hv : AdmissiblePartial.run p 0 q = some v) :
    ∃ c', Account p f (v 0) xs c' ∧ c ≤ c' := by
  obtain ⟨rfl,rfl⟩ := inactiveData ha (fun h => hn ((beforeActive k Γ q).1 h))
  exact ⟨1,.free (fun h => hn ((partialActive p k Γ q v hv).1 h)),le_rfl⟩

private theorem groundFreeTransport (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List (Carrier p)) (c : Nat)
    (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground)
    (ha : Account p f (before k [] Γ q) xs c) (hf : ordinalHeadFree q = true)
    (hv : AdmissiblePartial.run p 0 q = some v) :
    ∃ c', Account p f (v 0) xs c' ∧ c ≤ c' := by
  classical
  by_cases hq : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q
  · rw [AdmissiblePartial.run.eq_def,if_pos hf] at hv
    cases hv
    let F : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)) := .here
    have hc := adjacentCloseAccount p f k Γ q xs c ha
    have hclosed := (ActiveScalarAnnotation.Proof.active_headClosure F q).2 hq
    have hout : Active F (.add (ordinalHeadClosure q) .one) :=
      (activeAdd F _ _).2 (Or.inl hclosed)
    have hOne : Account p f (.one : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) [] 1 :=
      .free (inactiveOne F)
    refine ⟨c+2,?_,by omega⟩
    change Account p f (.add (ordinalHeadClosure q) .one) xs (c+2)
    simpa only [List.append_nil,Nat.add_assoc] using AccountWith.add hout hc hOne
  · exact inactiveTransport p f k Γ q xs c v hq ha hv

/-- Adjacent actual ground partial. This proof uses the actual ternary
shape lemma rather than any legacy default-policy account transport. -/
theorem adjacentAccountOfRun (p : Policy) (f : Nat → Nat) {k Γ}
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q) :
    ∀ (xs : List (Carrier p)) (c : Nat),
    Annotated p (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q →
    Account p f (before k [] Γ q) xs c →
    ∀ v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground,
      AdmissiblePartial.run p 0 q = some v →
      ∃ c' : Nat, Account p f (v 0) xs c' ∧ c ≤ c' := by
  classical
  induction ht with
  | @free q _ hn =>
    intro xs c _ ha v hv
    exact inactiveTransport p f k Γ q xs c v hn ha hv
  | tracked =>
    intro xs c _ ha v hv
    exact groundFreeTransport p f k Γ _ xs c v ha (by rfl) hv
  | @add a b ha hb iha ihb =>
    intro xs c hAnn hAcc v hv
    let F : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)) := .here
    by_cases hact : Active (.there F) (.add a b)
    · by_cases hf : ordinalHeadFree (.add a b) = true
      · exact groundFreeTransport p f k Γ _ xs c v hAcc hf hv
      · cases hAnn with
        | free hn => exact False.elim (hn hact)
        | add hAA hAB =>
          rw [AdmissiblePartial.run.eq_def,if_neg hf] at hv
          dsimp only at hv
          cases hvA : AdmissiblePartial.run p 0 a with
          | none => simp [hvA] at hv
          | some vA =>
            cases hvB : AdmissiblePartial.run p 0 b with
            | none => simp [hvA,hvB] at hv
            | some vB =>
              simp [hvA,hvB] at hv
              subst v
              change Account p f (.add (before k [] Γ a) (before k [] Γ b)) xs c at hAcc
              cases hAcc with
              | free hn => exact False.elim (hn ((beforeActive k Γ _).2 hact))
              | @add _ _ xs ys ca cb _ hca hcb =>
                obtain ⟨ca',hca',hleA⟩ := iha xs ca hAA hca vA hvA
                obtain ⟨cb',hcb',hleB⟩ := ihb ys cb hAB hcb vB hvB
                have hparts : Active F (vA 0) ∨ Active F (vB 0) :=
                  ((activeAdd (.there F) a b).1 hact).elim
                    (fun h => Or.inl ((partialActive p k Γ a vA hvA).2 h))
                    (fun h => Or.inr ((partialActive p k Γ b vB hvB).2 h))
                obtain ⟨cc,hcc,hle⟩ := accountThree p f (vA 0) (vB 0) xs ys ca' cb' hca' hcb' hparts
                exact ⟨cc,hcc,by omega⟩
    · exact inactiveTransport p f k Γ _ xs c v hact hAcc hv
  | @collapse h t hh ht ih =>
    intro xs c hAnn hAcc v hv
    let F : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)) := .here
    by_cases hact : Active (.there F) (.collapse h t)
    · by_cases hf : ordinalHeadFree (.collapse h t) = true
      · exact groundFreeTransport p f k Γ _ xs c v hAcc hf hv
      · cases hAnn with
        | free hn => exact False.elim (hn hact)
        | collapse op support hAT =>
          have htail : Active (.there F) t := ((activeCollapse (.there F) h t).1 hact).elim support id
          rw [AdmissiblePartial.run.eq_def,if_neg hf] at hv
          dsimp only at hv
          cases hvH : AdmissiblePartial.run p 1 h with
          | none => simp [hvH] at hv
          | some vH =>
            cases hvT : AdmissiblePartial.run p 0 t with
            | none => simp [hvH,hvT] at hv
            | some vT =>
              simp [hvH,hvT] at hv
              subst v
              have hout : Active F (.collapse (ordinalHeadClosure h) (vT 0)) :=
                (activeCollapse F _ _).2 (Or.inr ((partialActive p k Γ t vT hvT).2 htail))
              have hvMap := adjacentHeadMap f k Γ h
              have hsMap := adjacentSurplus k Γ h
              change Account p f (.collapse (before k [] Γ h) (before k [] Γ t)) xs c at hAcc
              cases hAcc with
              | free hn => exact False.elim (hn ((beforeActive k Γ _).2 hact))
              | @finite _ _ xs ct n _ hfinite hTail =>
                obtain ⟨ct',hTail',hle⟩ := ih xs ct hAT hTail vT hvT
                have hSum := AccountWith.finite hout (hvMap.trans hfinite) hTail'
                refine ⟨ct'+n+surplus (before k [] Γ h),?_,by omega⟩
                simpa only [Fin.val_zero,↓reduceIte,hsMap] using hSum
              | @nonfinite _ _ xs ct a _ hnonfinite hlabel _ hTail =>
                obtain ⟨ct',hTail',hle⟩ := ih xs ct hAT hTail vT hvT
                have hSum := AccountWith.nonfinite a hout (hvMap.symm ▸ hnonfinite)
                  (hlabel.trans hvMap.symm) (fun hb => by cases hb) hTail'
                refine ⟨ct'+surplus (before k [] Γ h),?_,by omega⟩
                simpa only [Fin.val_zero,↓reduceIte,hsMap] using hSum
    · exact inactiveTransport p f k Γ _ xs c v hact hAcc hv

theorem adjacentAccount (p : Policy) (f : Nat → Nat) {k Γ}
    (q : OrdinalExpression (.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List (Carrier p)) (c : Nat)
    (ht : ScalarTrees (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (ha : Annotated p (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (hac : Account p f (before k [] Γ q) xs c) :
    ∃ (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) .ground) (c' : Nat),
      AdmissiblePartial.run p 0 q = some v ∧ Account p f (v 0) xs c' ∧ c ≤ c' := by
  obtain ⟨v,hv,_⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated
    (Ty.curriedGround (k+1) :: Γ) .ground p 0 q (AdditiveHeadTree.Proof.scalar_grade ht)
  obtain ⟨c',hc',hle⟩ := adjacentAccountOfRun p f q ht xs c ha hac v hv
  exact ⟨v,c',hv,hc',hle⟩

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
