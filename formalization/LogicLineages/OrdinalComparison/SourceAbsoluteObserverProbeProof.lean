module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProfileProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open AdmissibleAssignment ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def innerTerm {Γ τ} (t : OriginalTerm Γ τ) (x : Variable Γ .ground) : OriginalTerm Γ τ :=
  .app (.lam (t.rename (Renaming.weaken Γ .ground))) (.var x)

theorem app_assignment {Γ σ τ} (f : OriginalTerm Γ (.arrow σ τ)) (g : OriginalTerm Γ σ)
    (vf : OrdinalVector Γ (Ty.arrow σ τ).level) (vg : OrdinalVector Γ σ.level)
    (hf : assignment OrdinalSyntax.defaultPolicy f = some vf)
    (hg : assignment OrdinalSyntax.defaultPolicy g = some vg) :
    assignment OrdinalSyntax.defaultPolicy (.app f g) = some (application OrdinalSyntax.defaultPolicy vf vg) := by
  change (assignment OrdinalSyntax.defaultPolicy f).bind
    (fun u => (assignment OrdinalSyntax.defaultPolicy g).bind
      (fun z => some (application OrdinalSyntax.defaultPolicy u z))) = _
  rw [hf, hg]
  rfl

theorem assigned_scalar {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat) (v : OrdinalVector Γ τ.level)
    (hv : assignment OrdinalSyntax.defaultPolicy t = some v) :
    ∃ n : Nat, 0 < n ∧ denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal) := by
  obtain ⟨w,n,hw,hn,he⟩ := source_scalar hΓ t ρ
  have h := Option.some.inj (hw.symm.trans hv)
  subst w
  exact ⟨n,hn,he⟩

theorem probe_comparison {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t s : OriginalTerm Γ τ) (x y : Variable Γ .ground) (ρ : OrdinalComponent Γ → Nat)
    (v w : OrdinalVector Γ τ.level)
    (ht : assignment OrdinalSyntax.defaultPolicy t = some v)
    (hs : assignment OrdinalSyntax.defaultPolicy s = some w)
    (n m : Nat)
    (hn : denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal))
    (hm : denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (w 0) = (m : Ordinal))
    (hpos : ∀ j, 0 < j.val →
      denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v j) =
      denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (w j))
    (p q : OrdinalVector Γ 0)
    (hp : assignment OrdinalSyntax.defaultPolicy (probe t x) = some p)
    (hq : assignment OrdinalSyntax.defaultPolicy (probe s y) = some q) :
    (denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (p 0) =
      denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (q 0)) ↔
      factor τ*n + (ρ ⟨.ground,x,0⟩+1) = factor τ*m + (ρ ⟨.ground,y,0⟩+1) := by
  let ν : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  let gx : OrdinalVector Γ 0 := fun j => .var ⟨.ground,x,j⟩
  let gy : OrdinalVector Γ 0 := fun j => .var ⟨.ground,y,j⟩
  let iv := application (σ := .ground) (τ := τ) OrdinalSyntax.defaultPolicy (unusedVector v) gx
  let iw := application (σ := .ground) (τ := τ) OrdinalSyntax.defaultPolicy (unusedVector w) gy
  have hiv : assignment OrdinalSyntax.defaultPolicy (innerTerm t x) = some iv :=
    app_assignment _ _ _ _ (unused_assignment t v ht) rfl
  have hiw : assignment OrdinalSyntax.defaultPolicy (innerTerm s y) = some iw :=
    app_assignment _ _ _ _ (unused_assignment s w hs) rfl
  obtain ⟨ni, hni, hvi⟩ := assigned_scalar hΓ (innerTerm t x) ρ iv hiv
  obtain ⟨mi, hmi, hwi⟩ := assigned_scalar hΓ (innerTerm s y) ρ iw hiw
  have hu := unused_positive_congr ν v w hpos
  have hg : ∀ j : Fin 1, 0 < j.val → denote ν (gx j) = denote ν (gy j) := by
    intro j hj
    have := j.isLt
    omega
  have hiHead := box_positive_congr ν 0
    (ordinalVectorAt (unusedVector v)) (ordinalVectorAt gx)
    (ordinalVectorAt (unusedVector w)) (ordinalVectorAt gy)
    (vectorAt_positive_congr ν _ _ hu) (vectorAt_positive_congr ν _ _ hg) 1 (by decide)
  obtain ⟨ci, hci⟩ := source_head_extraction hΓ (innerTerm t x) iv hiv _ _
    (by
      change application (σ := .ground) (τ := τ) OrdinalSyntax.defaultPolicy (unusedVector v) gx 0 = _
      exact application_scalar (σ := .ground) (τ := τ) (unusedVector v) gx)
  have htailv := box_tail_value ν 0 _ _ (unusedVector v 0) (gx 0)
    (unused_scalar ν v n hn) (show denote ν (gx 0) = ((ρ ⟨.ground,x,0⟩+1 : Nat) : Ordinal) from rfl)
  have htailw := box_tail_value ν 0 _ _ (unusedVector w 0) (gy 0)
    (unused_scalar ν w m hm) (show denote ν (gy 0) = ((ρ ⟨.ground,y,0⟩+1 : Nat) : Ordinal) from rfl)
  have hic := collapse_cancel ν _ _ _ _ ci hci hiHead _ _ htailv htailw
  have hiEq : denote ν (iv 0) = denote ν (iw 0) ↔
      factor τ*n + (ρ ⟨.ground,x,0⟩+1) = factor τ*m + (ρ ⟨.ground,y,0⟩+1) := by
    exact hic.trans (by omega)
  have hipos : ∀ j, 0 < j.val → denote ν (iv j) = denote ν (iw j) := by
    intro j hj
    exact (ground_application_positive ν _ _ j hj).trans
      ((hu _ hj).trans (ground_application_positive ν _ _ j hj).symm)
  let op : OriginalTerm Γ (.arrow τ .ground) := .lam .zeroC
  obtain ⟨ov, oe, hov, hoe, hove⟩ := source_scalar hΓ op ρ
  have hp' : assignment OrdinalSyntax.defaultPolicy (probe t x) =
      some (application OrdinalSyntax.defaultPolicy ov iv) := app_assignment _ _ _ _ hov hiv
  have hq' : assignment OrdinalSyntax.defaultPolicy (probe s y) =
      some (application OrdinalSyntax.defaultPolicy ov iw) := app_assignment _ _ _ _ hov hiw
  have hpp := Option.some.inj (hp.symm.trans hp')
  have hqq := Option.some.inj (hq.symm.trans hq')
  have hoHead := box_positive_congr ν τ.level (ordinalVectorAt ov) (ordinalVectorAt iv)
    (ordinalVectorAt ov) (ordinalVectorAt iw) (fun _ _ => rfl)
    (vectorAt_positive_congr ν _ _ hipos) 1 (by decide)
  obtain ⟨co,hco⟩ := source_head_extraction hΓ (probe t x)
    (application OrdinalSyntax.defaultPolicy ov iv) hp' _ _ (application_scalar (σ := τ) (τ := .ground) ov iv)
  have hotv := box_tail_value ν τ.level oe ni (ov 0) (iv 0) hove hvi
  have hotw := box_tail_value ν τ.level oe mi (ov 0) (iw 0) hove hwi
  have hoc := collapse_cancel ν _ _ _ _ co hco hoHead _ _ hotv hotw
  rw [hpp, hqq]
  change denote ν (.collapse _ _) = denote ν (.collapse _ _) ↔ _
  rw [hoc]
  have hiCast : (ni = mi) ↔ denote ν (iv 0) = denote ν (iw 0) := by
    rw [hvi,hwi]
    exact Nat.cast_inj.symm
  have he : oe+ni+τ.level = oe+mi+τ.level ↔ ni=mi := by omega
  exact he.trans (hiCast.trans hiEq)
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
