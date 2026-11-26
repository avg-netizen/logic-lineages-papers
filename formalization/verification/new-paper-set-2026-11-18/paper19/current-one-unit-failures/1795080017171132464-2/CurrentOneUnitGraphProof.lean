module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitScalarProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteAnchorProof
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationProof
public import LogicLineages.OrdinalComparison.WWSelectedBinderProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleAssignment ParametricSourceSuccessor

private theorem equationFree (τ : Ty) (d : Coefficients) (h : d.2.2 = true) :
    equation τ.level d = (1,0,0,d.1+1,d.1) := by
  simp [equation,h]

private theorem equationActive (τ : Ty) (d : Coefficients) (h : d.2.2 = false) :
    equation τ.level d = (OneUnit.coefficient τ*d.2.1,
      d.1*(4*OneUnit.copies τ*d.2.1+OneUnit.copies τ),d.1,
      OneUnit.coefficient τ*(d.2.1-d.1),0) := by
  simp [equation,h,OneUnit.coefficient,OneUnit.copies]

private theorem linearIdentity (τ : Ty) (d : Coefficients)
    (h : d.1 < d.2.1) (P R L L' : Nat)
    (hL : L = d.1*P+R)
    (hL' : L' = OneUnit.coefficient τ*d.2.1*P+OneUnit.coefficient τ*R+
      4*OneUnit.copies τ*d.2.1+OneUnit.copies τ) :
    (OneUnit.coefficient τ*d.2.1)*L+d.1*(4*OneUnit.copies τ*d.2.1+OneUnit.copies τ) =
      d.1*L'+(OneUnit.coefficient τ*(d.2.1-d.1))*R := by
  rw [hL,hL']
  have hd : d.1+(d.2.1-d.1) = d.2.1 := by omega
  rw [← hd]
  simp only [Nat.add_sub_cancel_left]
  ring

private theorem exactScalar (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {τ : Ty} (ρ : OrdinalComponent Γ → Nat)
    (a : OriginalTerm Γ τ) (r n : Nat) (hn : CurrentAbsolute.Scalar p f ρ a n) :
    CurrentAbsolute.Scalar p f ρ a r ↔ r = n :=
  ⟨fun hr => CurrentAbsolute.scalar_unique p f ρ a r n hr hn,fun h => h.symm ▸ hn⟩

theorem exactHeadGraph : CurrentOneUnitTargets.ExactHeadGraph := by
  intro p f Γ σ τ a hs
  obtain ⟨h,h',d,ha,hu,hd,hdata,hpos,hInfl,hsize⟩ := literalInflation p Γ σ τ a
  obtain ⟨g,g',v,v',hg,hg',hv,hv',hRows⟩ := actualScalarRows p f Γ σ τ a d hd
  have hp : 0 < OneUnit.coefficient τ := by unfold OneUnit.coefficient; omega
  cases hf : d.2.2 with
  | true =>
    refine ⟨d,hd,?_,?_,?_,?_⟩
    · rw [equationFree τ d hf]
      decide
    · rw [equationFree τ d hf]
      change 0 < d.1+1
      omega
    · intro hbad
      rw [hf] at hbad
      contradiction
    · intro ρ r
      obtain ⟨P,R,P',R',L,L',_,_,_,_,_,_,_,_,hR,_,hL,hL',_,_,hfree,_⟩ := hRows ρ
      have hL0 := (hfree hf).2
      rw [exactScalar p f (headUnitWires ρ) a r R hR]
      simp only [Formula,hf,↓reduceIte,equationFree τ d hf,holds,Nat.one_mul,Nat.zero_mul,Nat.zero_add,Nat.add_zero]
      constructor
      · rintro ⟨x,hx,he⟩
        have hxL := CurrentAbsolute.scalar_unique p f (ExistentialPlan.inputs ρ) (OneUnit.first a) x L hx hL
        rw [hxL] at he
        have hm : (d.1+1)*r = (d.1+1)*R := by omega
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ _) hm
      · rintro rfl
        exact ⟨L,hL,hL0⟩
  | false =>
    have hlt := (hsize hf).2.2
    have hpos' : 0 < d.2.1 := hpos.trans hlt
    have hc : 0 < OneUnit.coefficient τ*(d.2.1-d.1) := Nat.mul_pos hp (Nat.sub_pos_of_lt hlt)
    refine ⟨d,hd,?_,?_,?_,?_⟩
    · rw [equationActive τ d hf]
      exact Nat.mul_pos hp hpos'
    · rw [equationActive τ d hf]
      exact hc
    · intro _
      rw [equationActive τ d hf]
      exact hpos
    · intro ρ r
      obtain ⟨P,R,P',R',L,L',_,_,_,_,_,_,_,_,hR,_,hL,hL',hL0,_,_,hactive⟩ := hRows ρ
      have hi := linearIdentity τ d hlt P R L L' hL0 (hactive hf).2.2
      rw [exactScalar p f (headUnitWires ρ) a r R hR]
      simp only [Formula,hf,Bool.false_eq_true,↓reduceIte,equationActive τ d hf,holds,Nat.add_zero]
      constructor
      · rintro ⟨x,y,hx,hy,he⟩
        have hxL := CurrentAbsolute.scalar_unique p f (ExistentialPlan.inputs ρ) (OneUnit.first a) x L hx hL
        have hyL := CurrentAbsolute.scalar_unique p f (ExistentialPlan.inputs ρ) (OneUnit.second a) y L' hy hL'
        rw [hxL,hyL] at he
        have hm : (OneUnit.coefficient τ*(d.2.1-d.1))*r =
            (OneUnit.coefficient τ*(d.2.1-d.1))*R := by omega
        exact Nat.eq_of_mul_eq_mul_left hc hm
      · rintro rfl
        exact ⟨L,L',hL,hL',hi⟩

private theorem actualScalarRename (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ : List Ty} {τ : Ty} (r : Renaming Γ Δ)
    (ρ : OrdinalComponent Γ → Nat) (ν : OrdinalComponent Δ → Nat)
    (hr : ∀ c, ν (ordinalComponentRename r c) = ρ c)
    (t : OriginalTerm Γ τ) (n : Nat) :
    CurrentAbsolute.Scalar p f ν (t.rename r) n ↔ CurrentAbsolute.Scalar p f ρ t n := by
  obtain ⟨u,hu,_⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  have hraw := SourceRenaming.Proof.assignmentNaturality Γ Δ τ r p t
  rw [hu] at hraw
  have hv : assignment p (t.rename r) = some (SourceRenaming.renameVector r u) := hraw
  have he := PolicyObservation.expressionNaturality f Γ Δ r
    (fun c => ((ρ c+1 : Nat) : Ordinal)) (fun c => ((ν c+1 : Nat) : Ordinal))
    (fun σ x j => by rw [show ν ⟨σ,r x,j⟩ = ρ ⟨σ,x,j⟩ from hr ⟨σ,x,j⟩]) (u 0)
  constructor
  · rintro ⟨w,hw,hn⟩
    rw [hv] at hw
    cases Option.some.inj hw
    exact ⟨u,hu,he.symm.trans hn⟩
  · rintro ⟨w,hw,hn⟩
    rw [hu] at hw
    cases Option.some.inj hw
    exact ⟨_,hv,he.trans hn⟩

private theorem selectedUnitTransport (left right : List Ty) (σ : Ty) (hσ : 0 < σ.level)
    (ρ : Variable (left ++ σ :: right) .ground → Nat) :
    headUnitWires (σ:=σ) (UnitObservation.remainingInputs left right σ ρ) =
      SelectedBinder.transport left right σ (ExistentialPlan.inputs ρ) := by
  funext c
  rcases c with ⟨τ,x,j⟩
  cases x with
  | here =>
    cases σ with
    | ground => simp [Ty.level] at hσ
    | arrow a b => rfl
  | there x => cases τ <;> rfl

theorem exactSelectedGraph : CurrentOneUnitTargets.ExactSelectedGraph := by
  intro p f left right σ τ a hσ
  let b := a.rename (SelectedBinder.moveToHead left right σ)
  obtain ⟨d,hd,hA,hR,hB,h⟩ := exactHeadGraph p f (left++right) σ τ b hσ
  refine ⟨d,hd,hA,hR,hB,?_⟩
  intro ρ n
  let ρ' := UnitObservation.remainingInputs left right σ ρ
  have ht : ∀ c, headUnitWires ρ' (ordinalComponentRename (SelectedBinder.moveToHead left right σ) c) =
      ExistentialPlan.inputs ρ c := by
    rw [selectedUnitTransport left right σ hσ ρ]
    exact (SelectedBinder.Proof.valuationNaturality left right σ (ExistentialPlan.inputs ρ)).1
  exact (h ρ' n).trans (actualScalarRename p f (SelectedBinder.moveToHead left right σ)
    (ExistentialPlan.inputs ρ) (headUnitWires ρ') ht a n)

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
