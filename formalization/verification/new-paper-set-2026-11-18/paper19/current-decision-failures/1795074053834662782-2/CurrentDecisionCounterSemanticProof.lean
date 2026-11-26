module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterSemanticProof
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan PrimitiveLowering
open InputNormalization (sourceValue)
open CurrentDecisionEmitter

private noncomputable def twoEquations (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (a b : Input Γ .ground) (x y v : Variable Γ .ground)
    (k c : Nat) (ρ : Variable Γ .ground → Nat) : Prop :=
  sourceValue p f ρ a = sourceValue p f ρ b ∧ ρ x + k*ρ v = k*c + ρ y

private theorem counter_point (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool) {Γ σ τ}
    (hg : ∀ t ∈ Γ, t = Ty.ground) (a : Input Γ σ) (b : Input Γ τ) (A B : Nat)
    (ρ : Variable (Extension Γ) .ground → Nat) :
    (counterProgram strict hg a b A B).eval p f ρ Fin.elim0 ↔
    twoEquations p f (probes false hg a).1 (probes false hg a).2 (fresh 0) (fresh 1) (fresh 4)
      (AbsoluteObserver.factor σ) A ρ ∧
    twoEquations p f (probes true hg b).1 (probes true hg b).2 (fresh 2) (fresh 3) (fresh 5)
      (AbsoluteObserver.factor τ) B ρ ∧
    if strict then ρ (fresh 5) ≤ ρ (fresh 4) else ρ (fresh 5) < ρ (fresh 4) := by
  unfold counterProgram
  dsimp only
  apply observe_iff
  intro Δ r l ν hν hla hlb hlc hld
  apply observe_iff
  intro Ξ s rports μ hμ hra hrb hrc hrd
  rw [final_iff]
  simp only [mapPorts, hμ, hν, hla, hlb, hlc, hld, hra, hrb, hrc, hrd,
    SourceAST.sourceValue_rename p f r ρ ν hν, twoEquations]

private theorem values_after_place (right : Bool) {Γ}
    (ρ : Variable (Extension Γ) .ground → Nat) :
    let old := fun x : Variable Γ .ground => ρ (shift 6 x)
    let x : Variable (Extension Γ) .ground := if right then fresh 2 else fresh 0
    let y : Variable (Extension Γ) .ground := if right then fresh 3 else fresh 1
    let ν := ExistentialPlan.extend (ExistentialPlan.extend old (ρ y)) (ρ x)
    (∀ z, ρ (place right z) = ν z) ∧
    inputs ν = AbsoluteObserver.extend (inputs old) (ρ x) (ρ y) := by
  dsimp only
  constructor
  · intro z
    cases z with
    | here => rfl
    | there z =>
      cases z with
      | here => rfl
      | there z => rfl
  · funext c
    rcases c with ⟨σ,z,j⟩
    cases z with
    | here => rfl
    | there z =>
      cases z with
      | here => rfl
      | there z => cases σ <;> rfl

private theorem observe_place (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (right : Bool) (hg : ∀ t ∈ Γ, t = Ty.ground) (d : Input Γ τ)
    (ρ : Variable (Extension Γ) .ground → Nat) :
    let old := fun x : Variable Γ .ground => ρ (shift 6 x)
    let x : Variable (Extension Γ) .ground := if right then fresh 2 else fresh 0
    let y : Variable (Extension Γ) .ground := if right then fresh 3 else fresh 1
    let v : Variable (Extension Γ) .ground := if right then fresh 5 else fresh 4
    let raw := AbsoluteObserver.extend (inputs old) (ρ x) (ρ y)
    twoEquations p f (probes right hg d).1 (probes right hg d).2 x y v
      (AbsoluteObserver.factor τ) (CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩)) ρ ↔
      PolicyCollision.rawScalar p f raw (AbsoluteProbeDAG.originalInput d).term =
        PolicyCollision.rawScalar p f raw (AbsoluteProbeDAG.closedInput hg d).term ∧
      AbsoluteObserver.factor τ * ρ v + (ρ x+1) =
        AbsoluteObserver.factor τ * CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,d⟩) + (ρ y+1) := by
  dsimp only
  let old := fun x : Variable Γ .ground => ρ (shift 6 x)
  let x : Variable (Extension Γ) .ground := if right then fresh 2 else fresh 0
  let y : Variable (Extension Γ) .ground := if right then fresh 3 else fresh 1
  let ν := ExistentialPlan.extend (ExistentialPlan.extend old (ρ y)) (ρ x)
  have hv := (values_after_place right ρ).1
  have hr := (values_after_place right ρ).2
  unfold twoEquations probes
  dsimp only
  rw [SourceAST.sourceValue_rename p f (place right) ν ρ hv,
    SourceAST.sourceValue_rename p f (place right) ν ρ hv]
  have hx := (PolicyObservation.observationCalibration p f _ (inputs ν) (AbsoluteProbeDAG.originalInput d).term).1
  have hy := (PolicyObservation.observationCalibration p f _ (inputs ν) (AbsoluteProbeDAG.closedInput hg d).term).1
  unfold sourceValue
  rw [← hr]
  constructor
  · rintro ⟨he,hl⟩
    exact ⟨by omega,by omega⟩
  · rintro ⟨he,hl⟩
    exact ⟨by omega,by omega⟩

theorem counter_semantics (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (hf : FullAddition.Targets.SourceGrowth f) (strict : Bool) {Γ σ τ}
    (hg : ∀ t ∈ Γ, t = Ty.ground) (a : Input Γ σ) (b : Input Γ τ) :
    (∃ ρ, (counterProgram strict hg a b
        (CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,σ,a⟩))
        (CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,b⟩))).eval p f ρ Fin.elim0) ↔
    ∃ (ρ : Variable Γ .ground → Nat) (v w : Nat),
      CurrentAbsolute.Scalar p f (inputs ρ) a.term v ∧
      CurrentAbsolute.Scalar p f (inputs ρ) b.term w ∧
      (if strict then w ≤ v else w < v) := by
  let A := CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,σ,a⟩)
  let B := CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,b⟩)
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨hl,hr,he⟩ := (counter_point p f strict hg a b A B ρ).mp hρ
    let old := fun x : Variable Γ .ground => ρ (shift 6 x)
    have fl : CurrentAbsolute.Formula p f hg a (inputs old) (ρ (fresh 4)) := by
      have eq := (observe_place p f false hg a ρ).mp hl
      exact ⟨ρ (fresh 0),ρ (fresh 1),eq⟩
    have fr : CurrentAbsolute.Formula p f hg b (inputs old) (ρ (fresh 5)) := by
      have eq := (observe_place p f true hg b ρ).mp hr
      exact ⟨ρ (fresh 2),ρ (fresh 3),eq⟩
    exact ⟨old,_,_,(CurrentAbsolute.formulaExact p f hf Γ σ hg a _ _).mp fl,
      (CurrentAbsolute.formulaExact p f hf Γ τ hg b _ _).mp fr,he⟩
  · rintro ⟨old,v,w,hv,hw,he⟩
    obtain ⟨xl,yl,hl⟩ := (CurrentAbsolute.formulaExact p f hf Γ σ hg a _ _).mpr hv
    obtain ⟨xr,yr,hr⟩ := (CurrentAbsolute.formulaExact p f hf Γ τ hg b _ _).mpr hw
    let e := @ExistentialPlan.extend
    let ρ : Variable (Extension Γ) .ground → Nat := e _ (e _ (e _ (e _ (e _ (e _ old w) v) yr) xr) yl) xl
    refine ⟨ρ,(counter_point p f strict hg a b A B ρ).mpr ?_⟩
    exact ⟨(observe_place p f false hg a ρ).mpr hl,
      (observe_place p f true hg b ρ).mpr hr,he⟩

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
