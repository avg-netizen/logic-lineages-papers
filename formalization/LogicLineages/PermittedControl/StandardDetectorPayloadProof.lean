module
public import LogicLineages.PermittedControl.StandardDetectorAlignmentProof
public import LogicLineages.PermittedControl.StandardDetectorNumericProof
public import LogicLineages.PermittedControl.StandardApplicationEraserProof
public import LogicLineages.PermittedControl.CollapseProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open SelectedHardness (value0 value1)
open Source.FunctionalDetector (unary combine payload)
open Source.FunctionalDetector.Proof (omega_product_below)
noncomputable abbrev appValue := StandardDetectorNumeric.appValue

theorem values_facts {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary) :
    0 < value0 Phi p ρ a ∧ 0 < value1 Phi p ρ a ∧ value1 Phi p ρ a<epsilonZero ∧
      actualOrdinalNorm (value1 Phi p ρ a)≤value0 Phi p ρ a := by
  obtain ⟨v,hv,h0,h1,h⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  exact h

theorem values_assignment {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary) :
    ∃ v : OrdinalVector Γ 1, AdmissibleAssignment.assignment p a=some v ∧
      expressionValue Phi ρ (v 0)=(value0 Phi p ρ a : Ordinal) ∧ expressionValue Phi ρ (v 1)=value1 Phi p ρ a := by
  obtain ⟨v,hv,h0,h1,_⟩ := StandardSourceFacts.Proof.unaryFacts Γ p ρ a
  exact ⟨v,hv,h0,h1⟩

theorem ground_facts {Γ} (p : Policy) (a : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Phi Γ) :
    StandardApplicationEraser.GroundOutput p ρ a := StandardSourceFacts.Proof.groundFacts Γ p ρ a

theorem unaryApp {Γ} (p : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground) :
    groundValue Phi p ρ (.app a q)=appValue (value1 Phi p ρ a) (value0 Phi p ρ a) (groundValue Phi p ρ q) :=
  (StandardApplicationEraser.Proof.applicationCalibration Γ p ρ a q).2

theorem finite_tail_gap (a : Ordinal) (ha : a<epsilonZero) (s t : Nat) (hst : s≤t) :
    ParametricActualCollapse.collapseWith Phi (a+(s : Ordinal))+(t-s) ≤
      ParametricActualCollapse.collapseWith Phi (a+(t : Ordinal)) := by
  have h := collapse_finite_tail Phi (fun _ => le_rfl) (a+(s : Ordinal)) (t-s)
    (actualFiniteTailClosureNorm a ha s).1
  have he : a+(s : Ordinal)+((t-s : Nat) : Ordinal)=a+(t : Ordinal) := by
    rw [add_assoc,← Nat.cast_add,Nat.add_sub_of_le hst]
  rwa [he] at h

abbrev tail_gap_fourfold := StandardDetectorNumeric.Proof.finiteTails.2.2
abbrev head_domination := fun a b s t q ha hb hal hbl hab hn hs hq =>
  (StandardDetectorNumeric.Proof.headBudget a b s t q ha hb hal hbl hab hn hs hq).2
export StandardApplicationEraser.Proof (eraser_value ground_of_assignment)
theorem appValue_lower 
    (h : Ordinal) (he : h<epsilonZero) (s q : Nat) : s+q≤appValue h s q := by
  have hbound := collapse_finite_tail Phi (fun _ => le_rfl)
    (ordinalNaturalProduct Ordinal.omega0 h) (s+q) (omega_product_below h he)
  exact (Nat.le_add_left _ _).trans hbound

theorem unaryApp_lower  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a : OriginalTerm Γ unary)
    (q : OriginalTerm Γ .ground) :
    value0 Phi pol ρ a+groundValue Phi pol ρ q≤groundValue Phi pol ρ (.app a q) := by
  rw [unaryApp  pol]
  exact appValue_lower  _ (values_facts  pol ρ a).2.2.1 _ _

theorem zero_value  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) :
    groundValue Phi pol ρ (.zeroC : OriginalTerm Γ .ground)=1 := by
  apply ground_of_assignment Phi pol ρ _ (fun _ => .one) 1 rfl
  simp only [expressionValue,ParametricSourceSuccessor.denoteWith,Nat.cast_one]

/-- Four actual nested applications, all sharing the SAME literal payload.
The initial source zero has raw canonical scalar one. -/
theorem payload_bound  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    1+value0 Phi pol ρ (combine a a)+value0 Phi pol ρ (combine b b)+
      value0 Phi pol ρ (combine a b)+value0 Phi pol ρ (combine b a)≤groundValue Phi pol ρ (payload a b) := by
  have hX := unaryApp_lower  pol ρ (combine a a) (.zeroC : OriginalTerm Γ .ground)
  have hY := unaryApp_lower  pol ρ (combine b b) (.app (combine a a) .zeroC)
  have hZ := unaryApp_lower  pol ρ (combine a b) (.app (combine b b) (.app (combine a a) .zeroC))
  have hW := unaryApp_lower  pol ρ (combine b a)
    (.app (combine a b) (.app (combine b b) (.app (combine a a) .zeroC)))
  rw [zero_value  pol] at hX
  unfold payload
  omega

theorem payload_five  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    5≤groundValue Phi pol ρ (payload a b) := by
  have hb := payload_bound  pol ρ a b
  have hx := (values_facts  pol ρ (combine a a)).1
  have hy := (values_facts  pol ρ (combine b b)).1
  have hz := (values_facts  pol ρ (combine a b)).1
  have hw := (values_facts  pol ρ (combine b a)).1
  omega

theorem payload_components  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value0 Phi pol ρ (combine a a)≤groundValue Phi pol ρ (payload a b) ∧
    value0 Phi pol ρ (combine b b)≤groundValue Phi pol ρ (payload a b) ∧
    value0 Phi pol ρ (combine a b)≤groundValue Phi pol ρ (payload a b) ∧
    value0 Phi pol ρ (combine b a)≤groundValue Phi pol ρ (payload a b) := by
  have hb := payload_bound  pol ρ a b
  omega
end LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
