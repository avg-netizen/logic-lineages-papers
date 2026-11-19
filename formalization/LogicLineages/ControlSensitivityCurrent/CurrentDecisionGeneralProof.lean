module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCounterSyntaxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCounterSemanticProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionPositiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ExistentialPlan
open RawSourceDAG.InputCompiler (encodeInput)

private theorem scalarCoordinate (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat) (vec : OrdinalVector Γ τ.level)
    (ha : AdmissibleAssignment.assignment p t = some vec) (v : Nat)
    (h : CurrentAbsolute.Scalar p f ρ t v) :
    CurrentCounterBound.coordinate f vec (fun c => ρ c+1) 0 = (v : Ordinal) := by
  obtain ⟨other,he,hv⟩ := h
  rw [ha] at he
  cases Option.some.inj he
  exact hv

private theorem fixedAssignments (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool)
    {Γ σ τ} (a : Input Γ σ) (b : Input Γ τ)
    (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level)
    (ha : AdmissibleAssignment.assignment p a.term = some av)
    (hb : AdmissibleAssignment.assignment p b.term = some bv) :
    Universal p f strict a b ↔ ∀ ρ : Variable Γ .ground → Nat,
      CurrentCounterBound.compareAt f strict av bv (fun c => inputs ρ c+1) := by
  constructor
  · rintro ⟨av',bv',ha',hb',h⟩
    rw [ha] at ha'
    rw [hb] at hb'
    cases Option.some.inj ha'
    cases Option.some.inj hb'
    exact h
  · intro h
    exact ⟨av,bv,ha,hb,h⟩

private theorem scalarOrder (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool)
    {Γ σ τ} (a : Input Γ σ) (b : Input Γ τ)
    (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level)
    (ha : AdmissibleAssignment.assignment p a.term = some av)
    (hb : AdmissibleAssignment.assignment p b.term = some bv)
    (ρ : Variable Γ .ground → Nat) (v w : Nat)
    (hv : CurrentAbsolute.Scalar p f (inputs ρ) a.term v)
    (hw : CurrentAbsolute.Scalar p f (inputs ρ) b.term w) :
    (if strict then
      CurrentCounterBound.coordinate f av (fun c => inputs ρ c+1) 0 <
        CurrentCounterBound.coordinate f bv (fun c => inputs ρ c+1) 0
    else
      CurrentCounterBound.coordinate f av (fun c => inputs ρ c+1) 0 ≤
        CurrentCounterBound.coordinate f bv (fun c => inputs ρ c+1) 0) ↔
      if strict then v < w else v ≤ w := by
  rw [scalarCoordinate p f a.term (inputs ρ) av ha v hv,
      scalarCoordinate p f b.term (inputs ρ) bv hb w hw]
  cases strict <;> simp

private theorem counterNegation (strict : Bool) (v w : Nat) :
    (¬ (if strict then v < w else v ≤ w)) ↔ if strict then w ≤ v else w < v := by
  cases strict <;> simp

private theorem withPositive (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool)
    {Γ σ τ} (hg : ∀ t ∈ Γ, t = Ty.ground) (a : Input Γ σ) (b : Input Γ τ)
    (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level)
    (ha : AdmissibleAssignment.assignment p a.term = some av)
    (hb : AdmissibleAssignment.assignment p b.term = some bv)
    (hp : positiveTest p (strict,RawSourceDAG.encode ⟨Γ,σ,a⟩,RawSourceDAG.encode ⟨Γ,τ,b⟩) = true) :
    Universal p f strict a b ↔ ¬ ∃ (ρ : Variable Γ .ground → Nat) (v w : Nat),
      CurrentAbsolute.Scalar p f (inputs ρ) a.term v ∧
      CurrentAbsolute.Scalar p f (inputs ρ) b.term w ∧
      (if strict then w ≤ v else w < v) := by
  rw [fixedAssignments p f strict a b av bv ha hb]
  constructor
  · rintro h ⟨ρ,v,w,hv,hw,hn⟩
    exact (counterNegation strict v w).mpr hn
      ((scalarOrder p f strict a b av bv ha hb ρ v w hv hw).mp (h ρ).2)
  · intro h ρ
    have hpos := (positive_correct p f hg strict a b av bv ha hb (fun c => inputs ρ c+1)).mp hp
    obtain ⟨v,_,hv⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) a.term
    obtain ⟨w,_,hw⟩ := CurrentAbsolute.scalar_total p f (inputs ρ) b.term
    refine ⟨hpos,(scalarOrder p f strict a b av bv ha hb ρ v w hv hw).mpr ?_⟩
    by_contra hn
    exact h ⟨ρ,v,w,hv,hw,(counterNegation strict v w).mp hn⟩

private theorem transport (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ : List Ty} (h : Γ = Δ) (q : InputNormalization.Input Γ 0) :
    encodeInput (h ▸ q) = encodeInput q ∧
      ((∃ ρ, (h ▸ q : InputNormalization.Input Δ 0).eval p f ρ Fin.elim0) ↔
        ∃ ρ, q.eval p f ρ Fin.elim0) := by
  subst Δ
  exact ⟨rfl,Iff.rfl⟩

private theorem truthWitness (p : AdmissibleSum.Policy) (f : Nat → Nat) (Γ : List Ty) :
    ∃ ρ, (trueProgram Γ).eval p f ρ Fin.elim0 :=
  ⟨fun _ => 0, rfl⟩

theorem generalReduction : CurrentDecisionTargets.GeneralReduction := by
  intro p f hf strict n σ τ a b
  let Γ := List.replicate n Ty.ground
  let qa := RawSourceDAG.encode ⟨Γ,σ,a⟩
  let qb := RawSourceDAG.encode ⟨Γ,τ,b⟩
  let q : QueryCode := (strict,qa,qb)
  change ∃ r : InputNormalization.Input (List.replicate (n+6) Ty.ground) 0,
    toArithmetic p f q = (n+6,encodeInput r) ∧
      (Universal p f strict a b ↔ ¬ ∃ ρ, r.eval p f ρ Fin.elim0)
  have hlen : q.2.1.1.length = n := by
    change (Γ.map SyntaxCode.typeCode).length = n
    simp [Γ]
  have hg : ∀ t ∈ Γ, t = Ty.ground := fun _ ht => List.eq_of_mem_replicate ht
  obtain ⟨av,ha,_,_⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ σ a.term
  obtain ⟨bv,hb,_,_⟩ := PolicyAssignmentStatementChecks.full.2.2.1 p Γ τ b.term
  by_cases hp : positiveTest p q = true
  · let c := counterProgram strict hg a b (CurrentAbsolute.anchor p f qa) (CurrentAbsolute.anchor p f qb)
    have hctx : Extension Γ = List.replicate (n+6) Ty.ground := by
      change List.replicate 6 Ty.ground ++ List.replicate n Ty.ground = _
      rw [List.replicate_append_replicate, Nat.add_comm 6 n]
    let r : InputNormalization.Input (List.replicate (n+6) Ty.ground) 0 := hctx ▸ c
    obtain ⟨hc,he⟩ := transport p f hctx c
    have hsyntax : encodeInput c = counterCode p f q := counter_syntax p f strict hg a b
    refine ⟨r,?_,?_⟩
    · unfold toArithmetic
      rw [hlen,if_pos hp, hc, hsyntax]
    · change Universal p f strict a b ↔ ¬ ∃ ρ, (hctx ▸ c : InputNormalization.Input _ 0).eval p f ρ Fin.elim0
      rw [he, counter_semantics p f hf strict hg a b]
      exact withPositive p f strict hg a b av bv ha hb hp
  · let r := trueProgram (List.replicate (n+6) Ty.ground)
    refine ⟨r,?_,?_⟩
    · unfold toArithmetic
      rw [hlen,if_neg hp]
      rfl
    · have hfalse : ¬ Universal p f strict a b := by
        intro hu
        have h := (fixedAssignments p f strict a b av bv ha hb).mp hu (fun _ => 0)
        exact hp ((positive_correct p f hg strict a b av bv ha hb
          (fun c => inputs (fun _ => 0) c+1)).mpr h.1)
      exact ⟨fun hu => (hfalse hu).elim,fun hn => (hn (truthWitness p f _)).elim⟩

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
