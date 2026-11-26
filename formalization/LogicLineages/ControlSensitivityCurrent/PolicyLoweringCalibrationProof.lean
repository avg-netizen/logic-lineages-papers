module
public import LogicLineages.ControlSensitivityCurrent.PolicyLoweringTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyLowering
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open PrimitiveLowering SourceAdditionCompletion SourceSortCompletion
open ParametricSourceSuccessor
open ParametricSourceAddition.Proof (add_value collapse_one_value)
private def portExpression {Γ} : Port Γ → OrdinalExpression Γ
  | .zero => .one
  | .var x => .var ⟨.ground,x,0⟩
private theorem port_assignment (p : AdmissibleSum.Policy) {Γ} (a : Port Γ) :
    AdmissibleAssignment.assignment p a.term = some (fun _ => portExpression a) := by
  cases a with
  | zero => rfl
  | var x => apply congrArg some; funext i; have hi : i=0 := Fin.eq_zero i; subst i; rfl
private theorem successor_assignment (p : AdmissibleSum.Policy) {Γ} (a : Port Γ) :
    AdmissibleAssignment.assignment p (Expr.term (.successor a)) =
      some (fun _ => .collapse .one (.add .one (portExpression a))) := by
  change (some (fun _ => .one : OrdinalVector Γ 1)).bind
    (fun vf => (AdmissibleAssignment.assignment p a.term).bind
      (fun va => some (AdmissibleAssignment.application (σ:=.ground) (τ:=.ground) p vf va))) = _
  rw [port_assignment]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp [AdmissibleAssignment.application,AdmissibleAssignment.box,AdmissibleAssignment.boxTail,
    ordinalBoxPositive,ordinalVectorAt,Ty.level]
private theorem port_denote (f : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat) (a : Port Γ) :
    denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (portExpression a) = ((a.value ρ+1 : Nat) : Ordinal) := by
  cases a <;> simp [portExpression,Port.value,input,denoteWith]

theorem expressionCalibration : PolicyLoweringTargets.ExpressionCalibration := by
  intro p f hm hi Γ ρ e
  let ν : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  have h1 : denoteWith f ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denoteWith]
  cases e with
  | port a => exact ⟨_,port_assignment p a,port_denote f ρ a⟩
  | successor a =>
    refine ⟨_,successor_assignment p a,?_⟩
    have ht := add_value f ν _ _ _ _ h1 (port_denote f ρ a)
    have hc := collapse_one_value f hm hi ν _ _ ht
    have hn : 1+(a.value ρ+1)+2=a.value ρ+4 := by omega
    simpa only [numericValue,hn] using hc
  | erase a b =>
    refine ⟨_,PolicyGadget.atomicEraserAssignment p Γ a b,?_⟩
    exact ParametricSourceAddition.Proof.eraser_value f hm hi ρ a b
  | identityZero =>
    refine ⟨_,PolicyGadget.identityZeroAssignment p Γ,?_⟩
    have h2 := add_value f ν _ _ _ _ h1 h1
    have h3 := add_value f ν _ _ _ _ h2 h1
    have h4 := add_value f ν _ _ _ _ h3 h1
    exact collapse_one_value f hm hi ν _ _ h4
theorem equation_iff (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Expr Γ) :
    PolicyAddition.Equation p f ρ a.term b.term ↔ numericValue f ρ a = numericValue f ρ b := by
  obtain ⟨va,ha,hva⟩ := expressionCalibration p f hm hi _ ρ a
  obtain ⟨vb,hb,hvb⟩ := expressionCalibration p f hm hi _ ρ b
  constructor
  · rintro ⟨v,w,hv,hw,he⟩
    rw [ha] at hv
    rw [hb] at hw
    cases Option.some.inj hv
    cases Option.some.inj hw
    rw [hva,hvb] at he
    have hn := Nat.cast_injective he
    omega
  · intro he
    refine ⟨va,vb,ha,hb,?_⟩
    rw [hva,hvb,he]

@[simp] theorem port_equation (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Port Γ) :
    PolicyAddition.Equation p f ρ (Expr.port a).term (Expr.port b).term ↔ a.value ρ = b.value ρ :=
  equation_iff p f hm hi ρ _ _

@[simp] theorem successor_equation (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Port Γ) :
    PolicyAddition.Equation p f ρ (Expr.successor a).term (Expr.port b).term ↔ b.value ρ = f (a.value ρ+4) := by
  rw [equation_iff p f hm hi]
  exact eq_comm

@[simp] theorem erase_equation (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    PolicyAddition.Equation p f ρ (Expr.erase a b).term (Expr.erase c d).term ↔
      3*a.value ρ+b.value ρ = 3*c.value ρ+d.value ρ := by
  rw [equation_iff p f hm hi]
  change f _ = f _ ↔ _
  constructor
  · intro h
    have := hm.injective h
    omega
  · intro h
    congr 1
    omega

@[simp] theorem add_equations_exact (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    (∀ e ∈ addEquations a b c d, PolicyAddition.Equation p f ρ e.1.term e.2.term) ↔
      a.value ρ+b.value ρ=c.value ρ ∧ d.value ρ=3*b.value ρ := by
  simp [addEquations,erase_equation p f hm hi,Port.value]
  omega

@[simp] theorem successor_identity (p : AdmissibleSum.Policy) (f : Nat → Nat) (hm : StrictMono f) (hi : ∀ n : Nat, n ≤ f n) {Γ} (ρ : OrdinalComponent Γ → Nat) (a : Port Γ) :
    PolicyAddition.Equation p f ρ (Expr.successor a).term Expr.identityZero.term ↔ a.value ρ = 2 := by
  rw [equation_iff p f hm hi]
  change f (a.value ρ+4) = f 6 ↔ _
  constructor
  · intro h
    have := hm.injective h
    omega
  · intro h
    rw [h]

#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyLowering
end LogicLineages.ControlSensitivityCurrent.PolicyLowering
