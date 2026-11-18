module
public import LogicLineages.PermittedControl.SelectedDetectorPayloadProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorHeadOrderProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open Source.FunctionalDetector (unary combine payload left right)
open SelectedHardness (value0 value1)
open Source.FunctionalDetector.Proof (headCombine paddedHead sum_comm omega_product_below
  omega_product_norm omega_product_limit omega_product_strict headCombine_four headCombine_strict_left)

theorem combine_head {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (pol : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value1 ctrl pol ρ (combine a b)=headCombine (value1 ctrl pol ρ a) (value1 ctrl pol ρ b) := by
  rw [SelectedHardnessValuesProof.combine_head ctrl K hc pol,headCombine_four]
  rfl

theorem combine_scalar {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (pol : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    value0 ctrl pol ρ (combine a b)=ParametricActualCollapse.collapseWith ctrl
      (ordinalNaturalProduct Ordinal.omega0 (headCombine (value1 ctrl pol ρ a) (value1 ctrl pol ρ b))+
        ((9*value0 ctrl pol ρ a+5*value0 ctrl pol ρ b+13 : Nat) : Ordinal)) := by
  rw [SelectedHardnessValuesProof.combine_scalar ctrl K hc pol,headCombine_four]
  rfl

theorem app_strict_head (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (h k : Ordinal) (s t q : Nat) (hh : 0<h) (he : h<epsilonZero) (ke : k<epsilonZero)
    (hk : h<k) (hn : actualOrdinalNorm h≤s) (hs : s≤q) (hq : 5≤q) :
    4*appValue ctrl h s q<appValue ctrl k t q := by
  exact head_domination ctrl K hc _ _ s t q (omega_product_below h he) (omega_product_below k ke)
    (omega_product_limit h hh he) (omega_product_limit k (hh.trans hk) ke)
    (omega_product_strict h k he ke hk)
    ((omega_product_norm h he).trans (Nat.mul_le_mul_left 2 hn)) hs hq

theorem collapse_gap_two (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (h : Ordinal) (he : h<epsilonZero) (s t : Nat) (hst : s+2≤t) :
    ParametricActualCollapse.collapseWith ctrl (h+(s : Ordinal))+2≤
      ParametricActualCollapse.collapseWith ctrl (h+(t : Ordinal)) := by
  have hg := finite_tail_gap ctrl K hc h he s t (by omega)
  omega

theorem vector_equal_values (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    VectorEqual ctrl pol ρ a b ↔ value0 ctrl pol ρ a=value0 ctrl pol ρ b ∧ value1 ctrl pol ρ a=value1 ctrl pol ρ b := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ctrl K hc pol ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment ctrl K hc pol ρ b
  rw [vectorEqual_iff ctrl pol ρ a b av bv ha hb]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    rw [ha0,hb0] at h0
    rw [ha1,hb1] at h1
    exact ⟨by exact_mod_cast h0,h1⟩
  · rintro ⟨h0,h1⟩ j
    have hj : j=0 ∨ j=1 := by
      have h := j.isLt
      by_cases he : j.val=0
      · left; exact Fin.ext he
      · right; apply Fin.ext; simp only [Fin.val_one]; omega
    rcases hj with hj | hj <;> subst j
    · rw [ha0,hb0,h0]
    · rw [ha1,hb1,h1]

noncomputable def observedApp (ctrl : Nat → Nat) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b t : OriginalTerm Γ unary) : Nat := groundValue ctrl pol ρ (.app t (payload a b))

theorem app_head_dominates (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b s t : OriginalTerm Γ unary) (hst : value1 ctrl pol ρ s<value1 ctrl pol ρ t)
    (hs : value0 ctrl pol ρ s≤groundValue ctrl pol ρ (payload a b)) :
    4*observedApp ctrl pol ρ a b s<observedApp ctrl pol ρ a b t := by
  unfold observedApp
  rw [unaryApp ctrl K hc pol,unaryApp ctrl K hc pol]
  exact app_strict_head ctrl K hc _ _ _ _ _ (values_facts ctrl K hc pol ρ s).2.1
    (values_facts ctrl K hc pol ρ s).2.2.1 (values_facts ctrl K hc pol ρ t).2.2.1 hst
    (values_facts ctrl K hc pol ρ s).2.2.2 hs (payload_five ctrl K hc pol ρ a b)

theorem app_tail_dominates (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b s t : OriginalTerm Γ unary) (hh : value1 ctrl pol ρ s=value1 ctrl pol ρ t)
    (hs : value0 ctrl pol ρ s+2≤value0 ctrl pol ρ t) :
    4*observedApp ctrl pol ρ a b s<observedApp ctrl pol ρ a b t := by
  unfold observedApp
  rw [unaryApp ctrl K hc pol,unaryApp ctrl K hc pol]
  unfold appValue
  rw [hh]
  exact tail_gap_fourfold ctrl K hc _ (omega_product_below _ (values_facts ctrl K hc pol ρ t).2.2.1)
    (omega_product_limit _ (values_facts ctrl K hc pol ρ t).2.1 (values_facts ctrl K hc pol ρ t).2.2.1) _ _ _ hs

theorem combine_scalar_gap (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b c d : OriginalTerm Γ unary)
    (hh : headCombine (value1 ctrl pol ρ a) (value1 ctrl pol ρ b)=headCombine (value1 ctrl pol ρ c) (value1 ctrl pol ρ d))
    (ht : 9*value0 ctrl pol ρ a+5*value0 ctrl pol ρ b+13+2≤9*value0 ctrl pol ρ c+5*value0 ctrl pol ρ d+13) :
    value0 ctrl pol ρ (combine a b)+2≤value0 ctrl pol ρ (combine c d) := by
  rw [combine_scalar ctrl K hc pol,combine_scalar ctrl K hc pol,hh]
  apply collapse_gap_two ctrl K hc _ _ _ _ ht
  apply omega_product_below
  rw [← combine_head ctrl K hc pol]
  exact (values_facts ctrl K hc pol ρ (combine c d)).2.2.1

theorem headCombine_comm (a b : Ordinal) : headCombine a b=headCombine b a := by
  unfold headCombine
  rw [sum_comm (paddedHead a) (paddedHead b)]

theorem observed_equal (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b s t : OriginalTerm Γ unary)
    (h0 : value0 ctrl pol ρ s=value0 ctrl pol ρ t) (h1 : value1 ctrl pol ρ s=value1 ctrl pol ρ t) :
    observedApp ctrl pol ρ a b s=observedApp ctrl pol ρ a b t := by
  unfold observedApp
  rw [unaryApp ctrl K hc pol,unaryApp ctrl K hc pol,h0,h1]

theorem left_value (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    groundValue ctrl pol ρ (left a b)=
      ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0 + ((3*observedApp ctrl pol ρ a b (combine a a)+observedApp ctrl pol ρ a b (combine b b)+2 : Nat) : Ordinal)) :=
  eraser_value ctrl K hc pol ρ _ _

theorem right_value (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    groundValue ctrl pol ρ (right a b)=
      ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0 + ((3*observedApp ctrl pol ρ a b (combine a b)+observedApp ctrl pol ρ a b (combine b a)+2 : Nat) : Ordinal)) :=
  eraser_value ctrl K hc pol ρ _ _
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
