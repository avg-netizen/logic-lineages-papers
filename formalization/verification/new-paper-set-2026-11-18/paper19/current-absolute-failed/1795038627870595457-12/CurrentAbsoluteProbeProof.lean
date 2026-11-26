module
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteProfileProof
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperProof
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAbsolute

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.PermittedControl
open GroundEquivalence AdmissibleAssignment ParametricSourceSuccessor
open SelectedHardnessUnusedProof (unused_assignment unusedVector)

private theorem app_assignment (p : AdmissibleSum.Policy) {Γ σ τ}
    (a : OriginalTerm Γ (.arrow σ τ)) (b : OriginalTerm Γ σ)
    (av : OrdinalVector Γ (Ty.arrow σ τ).level) (bv : OrdinalVector Γ σ.level)
    (ha : assignment p a = some av) (hb : assignment p b = some bv) :
    assignment p (.app a b) = some (application p av bv) := by
  simp [assignment, ha, hb]
  rfl

private theorem scalar_of (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment p t = some v) :
    ∃ n : Nat, denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal) := by
  obtain ⟨n,_,w,hw,hn⟩ := scalar_total p f ρ t
  rw [hv] at hw
  cases Option.some.inj hw
  exact ⟨n,hn⟩

private theorem app_scalar (p : AdmissibleSum.Policy) {Γ σ τ}
    (a : OrdinalVector Γ (Ty.arrow σ τ).level) (b : OrdinalVector Γ σ.level) :
    application p a b 0 =
      .collapse (ordinalBoxPositive σ.level (ordinalVectorAt a) (ordinalVectorAt b) 1)
        (boxTail p σ.level (a 0) (b 0)) := rfl

private theorem head_grade (p : AdmissibleSum.Policy) {Γ τ} (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment p t = some v)
    (a b : OrdinalExpression Γ) (he : v 0 = .collapse a b) : GeneratedOrdinalGrade Γ 1 a := by
  obtain ⟨w,hw,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  rw [hv] at hw
  cases Option.some.inj hw
  have hg0 : GeneratedOrdinalGrade Γ 0 (v 0) := hg 0
  rw [he] at hg0
  cases hg0 with
  | collapse h _ => exact h

private theorem probe_pair (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) {Γ τ}
    (t s : OriginalTerm Γ τ) (x y : Variable Γ .ground) (ρ : OrdinalComponent Γ → Nat)
    (v w : OrdinalVector Γ τ.level) (ht : assignment p t = some v) (hs : assignment p s = some w)
    (n m : Nat)
    (hn : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal))
    (hm : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (w 0) = (m : Ordinal))
    (hpos : ∀ j, 0 < j.val →
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v j) =
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (w j)) :
    PolicyCollision.rawScalar p f ρ (AbsoluteObserver.probe t x) =
      PolicyCollision.rawScalar p f ρ (AbsoluteObserver.probe s y) ↔
    AbsoluteObserver.factor τ*n + (ρ ⟨.ground,x,0⟩+1) =
      AbsoluteObserver.factor τ*m + (ρ ⟨.ground,y,0⟩+1) := by
  let ν : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  let tx : OriginalTerm Γ τ := .app (.lam (t.rename (Renaming.weaken Γ .ground))) (.var x)
  let sy : OriginalTerm Γ τ := .app (.lam (s.rename (Renaming.weaken Γ .ground))) (.var y)
  let gx : OrdinalVector Γ 0 := fun j => .var ⟨.ground,x,j⟩
  let gy : OrdinalVector Γ 0 := fun j => .var ⟨.ground,y,j⟩
  let iv := application (σ := .ground) (τ := τ) p (unusedVector p v) gx
  let iw := application (σ := .ground) (τ := τ) p (unusedVector p w) gy
  have hv : assignment p tx = some iv :=
    app_assignment p _ _ _ _ (unused_assignment p t v ht) rfl
  have hw : assignment p sy = some iw :=
    app_assignment p _ _ _ _ (unused_assignment p s w hs) rfl
  obtain ⟨ni, hvi⟩ := scalar_of p f ρ tx iv hv
  obtain ⟨mi, hwi⟩ := scalar_of p f ρ sy iw hw
  have hu := unused_positive f p ν v w hpos
  have htrivial : ∀ j : Fin 1, 0 < j.val → denoteWith f ν (gx j) = denoteWith f ν (gy j) := by
    intro j hj
    have := j.isLt
    omega
  have hiHead := box_head_congr f ν 0
    (ordinalVectorAt (unusedVector p v)) (ordinalVectorAt gx)
    (ordinalVectorAt (unusedVector p w)) (ordinalVectorAt gy)
    (positive_congr f ν _ _ hu) (positive_congr f ν _ _ htrivial) 1 (by decide)
  have hgrade := head_grade p tx iv hv _ _ (app_scalar p (unusedVector p v) gx)
  have htailv := box_tail_value f p ν 0 _ _ (unusedVector p v 0) (gx 0)
    (unused_scalar f p ν v n hn)
    (show denoteWith f ν (gx 0) = ((ρ ⟨.ground,x,0⟩+1 : Nat) : Ordinal) from rfl)
  have htailw := box_tail_value f p ν 0 _ _ (unusedVector p w 0) (gy 0)
    (unused_scalar f p ν w m hm)
    (show denoteWith f ν (gy 0) = ((ρ ⟨.ground,y,0⟩+1 : Nat) : Ordinal) from rfl)
  have hic := collapse_cancel f hf ρ _ _ _ _ hgrade hiHead _ _ htailv htailw
  have hiEq : denoteWith f ν (iv 0) = denoteWith f ν (iw 0) ↔
      AbsoluteObserver.factor τ*n + (ρ ⟨.ground,x,0⟩+1) =
        AbsoluteObserver.factor τ*m + (ρ ⟨.ground,y,0⟩+1) := by
    change denoteWith f ν (application p (unusedVector p v) gx 0) =
      denoteWith f ν (application p (unusedVector p w) gy 0) ↔ _
    rw [app_scalar, app_scalar]
    exact hic.trans (by omega)
  have hiPos : ∀ j, 0 < j.val → denoteWith f ν (iv j) = denoteWith f ν (iw j) := by
    intro j hj
    exact (ground_app_positive f p ν _ _ j hj).trans
      ((hu _ hj).trans (ground_app_positive f p ν _ _ j hj).symm)
  let op : OriginalTerm Γ (.arrow τ .ground) := .lam .zeroC
  obtain ⟨ov,hov,hog⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow τ .ground) p op
  obtain ⟨oe,hove⟩ := scalar_of p f ρ op ov hov
  let av := application (σ := τ) (τ := .ground) p ov iv
  let bv := application (σ := τ) (τ := .ground) p ov iw
  have hleft : assignment p (AbsoluteObserver.probe t x) = some av :=
    app_assignment p _ _ _ _ hov hv
  have hright : assignment p (AbsoluteObserver.probe s y) = some bv :=
    app_assignment p _ _ _ _ hov hw
  have houtHead := box_head_congr f ν τ.level
    (ordinalVectorAt ov) (ordinalVectorAt iv) (ordinalVectorAt ov) (ordinalVectorAt iw)
    (fun _ _ => rfl) (positive_congr f ν _ _ hiPos) 1 (by decide)
  have houter := head_grade p (AbsoluteObserver.probe t x) av hleft _ _ (app_scalar p ov iv)
  have hotv := box_tail_value f p ν τ.level oe ni (ov 0) (iv 0) hove hvi
  have hotw := box_tail_value f p ν τ.level oe mi (ov 0) (iw 0) hove hwi
  have hoc := collapse_cancel f hf ρ _ _ _ _ houter houtHead _ _ hotv hotw
  have eqRaw : PolicyCollision.rawScalar p f ρ (AbsoluteObserver.probe t x) =
      PolicyCollision.rawScalar p f ρ (AbsoluteObserver.probe s y) ↔
      denoteWith f ν (av 0) = denoteWith f ν (bv 0) := by
    obtain ⟨xx,hx⟩ := scalar_of p f ρ _ av hleft
    obtain ⟨yy,hy⟩ := scalar_of p f ρ _ bv hright
    rw [PolicyOrderWrapper.raw_of_scalar p f ρ _ _ ⟨av,hleft,hx⟩,
      PolicyOrderWrapper.raw_of_scalar p f ρ _ _ ⟨bv,hright,hy⟩, hx, hy]
    exact Nat.cast_inj.symm
  rw [eqRaw]
  change denoteWith f ν (application p ov iv 0) = denoteWith f ν (application p ov iw 0) ↔ _
  rw [app_scalar, app_scalar, hoc]
  have hiCast : ni = mi ↔ denoteWith f ν (iv 0) = denoteWith f ν (iw 0) := by
    rw [hvi,hwi]
    exact Nat.cast_inj.symm
  have he : oe+ni+τ.level = oe+mi+τ.level ↔ ni=mi := by omega
  exact he.trans (hiCast.trans hiEq)

theorem probeIdentity : CurrentAbsoluteTargets.ProbeIdentity := by
  intro p f hf Γ τ hg d ρ n x y hscalar
  obtain ⟨v,hv,hn⟩ := hscalar
  obtain ⟨_,w,hw,hc⟩ := anchorExact p f hf Γ τ hg d
  let Δ := Ty.ground :: Ty.ground :: Γ
  let σ := AbsoluteObserver.extend ρ x y
  let rl : Renaming Γ Δ := AbsoluteObserver.shiftTwo Γ
  let rr : Renaming [] Δ := AbsoluteObserver.fromEmpty Δ
  let vl := SourceRenaming.renameVector rl v
  let wr := SourceRenaming.renameVector rr w
  have ha : assignment p (d.term.rename rl) = some vl := by
    rw [SourceRenaming.Proof.assignmentNaturality, hv]
    rfl
  have hb : assignment p ((AbsoluteObserver.close hg d.term).rename rr) = some wr := by
    rw [SourceRenaming.Proof.assignmentNaturality, hw]
    rfl
  let ν : OrdinalComponent Δ → Ordinal := fun c => ((σ c+1 : Nat) : Ordinal)
  have lv (j : Fin (τ.level+1)) : denoteWith f ν (vl j) =
      denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v j) :=
    PolicyObservation.expressionNaturality f Γ Δ rl _ ν (fun _ _ _ => rfl) _
  have rv (j : Fin (τ.level+1)) : denoteWith f ν (wr j) =
      denoteWith f (fun _ => 1) (w j) :=
    PolicyObservation.expressionNaturality f [] Δ rr _ ν (fun _ a _ => nomatch a) _
  have hrv : denoteWith f ν (wr 0) = (anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩) : Ordinal) := by
    rw [rv]
    simpa only [Nat.zero_add, Nat.cast_one] using hc
  have hpos : ∀ j, 0 < j.val → denoteWith f ν (vl j) = denoteWith f ν (wr j) := by
    have e := closure_assignment p hg d.term v hv
    rw [hw] at e
    have he := Option.some.inj e
    obtain ⟨c, hcv, hg'⟩ := actualAdmissibleAssignmentGenerated Γ τ p d.term
    rw [hv] at hcv
    cases Option.some.inj hcv
    intro j hj
    rw [lv, rv, he]
    change denoteWith f _ (v j) =
      denoteWith f _ (GroundClosing.expression (AbsoluteObserver.closingMap hg) (v j))
    rw [closing_value]
    exact closed_value f _ (actualGeneratedGroundPositiveClosed Γ hg _ _ hj (hg' j)) _ _
  dsimp only
  rw [ (AbsoluteProbeDAG.Proof.original Γ τ d).1, (AbsoluteProbeDAG.Proof.closed Γ τ hg d).1]
  change PolicyCollision.rawScalar p f σ (AbsoluteObserver.probe (d.term.rename rl) .here) =
    PolicyCollision.rawScalar p f σ (AbsoluteObserver.probe ((AbsoluteObserver.close hg d.term).rename rr) (.there .here)) ↔ _
  exact probe_pair p f hf _ _ .here (.there .here) σ vl wr ha hb n _
    ((lv 0).trans hn) hrv hpos

end LogicLineages.ControlSensitivityCurrent.CurrentAbsolute
