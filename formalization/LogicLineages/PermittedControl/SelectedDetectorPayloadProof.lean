module
public import LogicLineages.PermittedControl.SelectedDetectorApplicationProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain
open SelectedHardness (value0 value1)
open Source.FunctionalDetector (unary combine payload)
open Source.FunctionalDetector.Proof (omega_product_below)

theorem appValue_lower (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (h : Ordinal) (he : h<epsilonZero) (s q : Nat) : s+q≤appValue ctrl h s q := by
  have hbound := collapse_finite_tail ctrl (selected_threshold_admissible ctrl K hc).2
    (ordinalNaturalProduct Ordinal.omega0 h) (s+q) (omega_product_below h he)
  exact (Nat.le_add_left _ _).trans hbound

theorem unaryApp_lower (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    value0 ctrl pol ρ a+groundValue ctrl pol ρ q≤groundValue ctrl pol ρ (.app a q) := by
  rw [unaryApp ctrl K hc pol]
  exact appValue_lower ctrl K hc _ (values_facts ctrl K hc pol ρ a).2.2.1 _ _

theorem zero_value (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) :
    groundValue ctrl pol ρ (.zeroC : OriginalTerm Γ .ground)=1 := by
  apply ground_of_assignment ctrl pol ρ _ (fun _ => .one) 1 rfl
  simp only [expressionValue,ParametricSourceSuccessor.denoteWith,Nat.cast_one]

/-- Four actual nested applications, all sharing the SAME literal payload.
The initial source zero has raw canonical scalar one. -/
theorem payload_bound (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    1+value0 ctrl pol ρ (combine a a)+value0 ctrl pol ρ (combine b b)+
      value0 ctrl pol ρ (combine a b)+value0 ctrl pol ρ (combine b a)≤groundValue ctrl pol ρ (payload a b) := by
  have hX := unaryApp_lower ctrl K hc pol ρ (combine a a) (.zeroC : OriginalTerm Γ .ground)
  have hY := unaryApp_lower ctrl K hc pol ρ (combine b b) (.app (combine a a) .zeroC)
  have hZ := unaryApp_lower ctrl K hc pol ρ (combine a b) (.app (combine b b) (.app (combine a a) .zeroC))
  have hW := unaryApp_lower ctrl K hc pol ρ (combine b a)
    (.app (combine a b) (.app (combine b b) (.app (combine a a) .zeroC)))
  rw [zero_value ctrl K hc pol] at hX
  unfold payload
  omega

theorem payload_five (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    5≤groundValue ctrl pol ρ (payload a b) := by
  have hb := payload_bound ctrl K hc pol ρ a b
  have hx := (values_facts ctrl K hc pol ρ (combine a a)).1
  have hy := (values_facts ctrl K hc pol ρ (combine b b)).1
  have hz := (values_facts ctrl K hc pol ρ (combine a b)).1
  have hw := (values_facts ctrl K hc pol ρ (combine b a)).1
  omega

theorem payload_components (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value0 ctrl pol ρ (combine a a)≤groundValue ctrl pol ρ (payload a b) ∧
    value0 ctrl pol ρ (combine b b)≤groundValue ctrl pol ρ (payload a b) ∧
    value0 ctrl pol ρ (combine a b)≤groundValue ctrl pol ρ (payload a b) ∧
    value0 ctrl pol ρ (combine b a)≤groundValue ctrl pol ρ (payload a b) := by
  have hb := payload_bound ctrl K hc pol ρ a b
  omega
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
