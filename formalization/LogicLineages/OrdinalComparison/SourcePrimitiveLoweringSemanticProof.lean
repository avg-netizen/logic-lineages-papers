module
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringTargets
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionSemanticProof
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionIdentityProof
public import LogicLineages.OrdinalComparison.SourceSuccessorCodingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open AdmissibleAssignment SourceAdditionCompletion SourceSortCompletion
attribute [local irreducible] Phi actualCollapse

def portExpression {Γ} : Port Γ → OrdinalExpression Γ
  | .zero => .one
  | .var x => .var ⟨.ground,x,0⟩

theorem port_assignment {Γ} (a : Port Γ) :
    assignment OrdinalSyntax.defaultPolicy a.term = some (fun _ => portExpression a) := by
  cases a with
  | zero => rfl
  | var x =>
      apply congrArg some
      funext i
      have hi : i=0 := Fin.eq_zero i
      subst i
      rfl

theorem port_denote {Γ} (ρ : OrdinalComponent Γ → Nat) (a : Port Γ) :
    denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (portExpression a) = ((a.value ρ+1 : Nat) : Ordinal) := by
  cases a <;> simp [portExpression,Port.value,input,denote]

noncomputable def numericValue {Γ} (ρ : OrdinalComponent Γ → Nat) : Expr Γ → Nat
  | .port a => a.value ρ
  | .successor a => successorObservation (a.value ρ)
  | .erase a b => Phi (3*a.value ρ+b.value ρ+8)
  | .identityZero => Phi 6

theorem successor_assignment {Γ} (a : Port Γ) :
    assignment OrdinalSyntax.defaultPolicy (Expr.term (.successor a)) =
      some (fun _ => .collapse .one (.add .one (portExpression a))) := by
  change (some (fun _ => .one : OrdinalVector Γ 1)).bind
    (fun vf => (assignment OrdinalSyntax.defaultPolicy a.term).bind
      (fun va => some (application (σ := .ground) (τ := .ground) OrdinalSyntax.defaultPolicy vf va))) = _
  rw [port_assignment]
  apply congrArg some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp [application,box,boxTail,ordinalBoxPositive,ordinalVectorAt,Ty.level]

theorem expr_calibration {Γ} (ρ : OrdinalComponent Γ → Nat) (e : Expr Γ) :
    ∃ v : OrdinalVector Γ 0, assignment OrdinalSyntax.defaultPolicy e.term = some v ∧
      denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = ((numericValue ρ e+1 : Nat) : Ordinal) := by
  let ν : OrdinalComponent Γ → Ordinal := fun c => ((ρ c+1 : Nat) : Ordinal)
  have h1 : denote ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denote]
  cases e with
  | port a => exact ⟨_,port_assignment a,port_denote ρ a⟩
  | successor a =>
      refine ⟨_,successor_assignment a,?_⟩
      have ha := port_denote ρ a
      have ht := SourceAdditionCompletion.Proof.add_value ν _ _ _ _ h1 ha
      have hc := SourceAdditionCompletion.Proof.collapse_one_value ν _ _ ht
      have hn : 1+(a.value ρ+1)+2 = a.value ρ+4 := by omega
      simpa only [numericValue,(SourceSuccessorCodingProof.successorObservationCalibration (a.value ρ)).2,hn] using hc
  | erase a b =>
      have he := SourceCollisionCompletion.Proof.eraser_assignment a.term b.term
        (fun _ => portExpression a) (fun _ => portExpression b) (port_assignment a) (port_assignment b)
      refine ⟨_,he,?_⟩
      have hd := SourceCollisionCompletion.Proof.eraser_denotation ν (portExpression a) (portExpression b)
        (a.value ρ+1) (b.value ρ+1) (port_denote ρ a) (port_denote ρ b)
      rw [SourceCollisionCompletion.Proof.g_calibration] at hd
      have hn : 3*(a.value ρ+1)+(b.value ρ+1)+2+2 = 3*a.value ρ+b.value ρ+8 := by omega
      simpa only [numericValue,hn] using hd
  | identityZero =>
      refine ⟨_,SourceAdditionCompletion.Proof.identity_zero_assignment Γ,?_⟩
      have h2 := SourceAdditionCompletion.Proof.add_value ν _ _ _ _ h1 h1
      have h3 := SourceAdditionCompletion.Proof.add_value ν _ _ _ _ h2 h1
      have h4 := SourceAdditionCompletion.Proof.add_value ν _ _ _ _ h3 h1
      exact SourceAdditionCompletion.Proof.collapse_one_value ν _ _ h4

theorem equation_iff {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Expr Γ) :
    Equation ρ a.term b.term ↔ numericValue ρ a = numericValue ρ b := by
  obtain ⟨va,ha,hva⟩ := expr_calibration ρ a
  obtain ⟨vb,hb,hvb⟩ := expr_calibration ρ b
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

@[simp] theorem port_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Port Γ) :
    Equation ρ (Expr.port a).term (Expr.port b).term ↔ a.value ρ = b.value ρ :=
  equation_iff ρ _ _

@[simp] theorem successor_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b : Port Γ) :
    Equation ρ (Expr.successor a).term (Expr.port b).term ↔ b.value ρ = successorObservation (a.value ρ) := by
  rw [equation_iff]
  exact eq_comm

@[simp] theorem erase_equation {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    Equation ρ (Expr.erase a b).term (Expr.erase c d).term ↔
      3*a.value ρ+b.value ρ = 3*c.value ρ+d.value ρ := by
  rw [equation_iff]
  change Phi _ = Phi _ ↔ _
  constructor
  · intro h
    have := Phi_strictMono.injective h
    omega
  · intro h
    congr 1
    omega

@[simp] theorem add_equations_exact {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Port Γ) :
    (∀ e ∈ addEquations a b c d, Equation ρ e.1.term e.2.term) ↔
      a.value ρ+b.value ρ=c.value ρ ∧ d.value ρ=3*b.value ρ := by
  simp [addEquations,Port.value]
  omega

@[simp] theorem successor_identity {Γ} (ρ : OrdinalComponent Γ → Nat) (a : Port Γ) :
    Equation ρ (Expr.successor a).term Expr.identityZero.term ↔ a.value ρ = 2 := by
  rw [equation_iff]
  change successorObservation (a.value ρ) = Phi 6 ↔ _
  rw [(SourceSuccessorCodingProof.successorObservationCalibration (a.value ρ)).2]
  constructor
  · intro h
    have := Phi_strictMono.injective h
    omega
  · intro h
    rw [h]
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering.Proof
