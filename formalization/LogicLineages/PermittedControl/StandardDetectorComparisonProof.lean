module
public import LogicLineages.PermittedControl.StandardDetectorPayloadProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorHeadOrderProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain SelectedFunctionalDetector
open Source.FunctionalDetector (unary combine payload left right)
open SelectedHardness (value0 value1)
open Source.FunctionalDetector.Proof (headCombine paddedHead sum_comm omega_product_below
  omega_product_norm omega_product_limit omega_product_strict headCombine_four headCombine_strict_left)
theorem combine_head {Γ} 
    (pol : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value1 Phi pol ρ (combine a b)=headCombine (value1 Phi pol ρ a) (value1 Phi pol ρ b) := by
  rw [StandardCombinatorCoordinates.Proof.combine_head  pol,headCombine_four]
  rfl

theorem combine_scalar {Γ} 
    (pol : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    value0 Phi pol ρ (combine a b)=ParametricActualCollapse.collapseWith Phi
      (ordinalNaturalProduct Ordinal.omega0 (headCombine (value1 Phi pol ρ a) (value1 Phi pol ρ b))+
        ((9*value0 Phi pol ρ a+5*value0 Phi pol ρ b+13 : Nat) : Ordinal)) := by
  rw [StandardCombinatorCoordinates.Proof.combine_scalar  pol,headCombine_four]
  rfl

theorem app_strict_head 
    (h k : Ordinal) (s t q : Nat) (hh : 0<h) (he : h<epsilonZero) (ke : k<epsilonZero)
    (hk : h<k) (hn : actualOrdinalNorm h≤s) (hs : s≤q) (hq : 5≤q) :
    4*appValue h s q<appValue k t q := by
  exact head_domination  _ _ s t q (omega_product_below h he) (omega_product_below k ke)
    (omega_product_limit h hh he) (omega_product_limit k (hh.trans hk) ke)
    (omega_product_strict h k he ke hk)
    ((omega_product_norm h he).trans (Nat.mul_le_mul_left 2 hn)) hs hq

theorem collapse_gap_two 
    (h : Ordinal) (he : h<epsilonZero) (s t : Nat) (hst : s+2≤t) :
    ParametricActualCollapse.collapseWith Phi (h+(s : Ordinal))+2≤
      ParametricActualCollapse.collapseWith Phi (h+(t : Ordinal)) := by
  have hg := finite_tail_gap  h he s t (by omega)
  omega

theorem vector_equal_values  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    VectorEqual Phi pol ρ a b ↔ value0 Phi pol ρ a=value0 Phi pol ρ b ∧ value1 Phi pol ρ a=value1 Phi pol ρ b := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment  pol ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment  pol ρ b
  rw [vectorEqual_iff Phi pol ρ a b av bv ha hb]
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

noncomputable def observedApp (Phi : Nat → Nat) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b t : OriginalTerm Γ unary) : Nat := groundValue Phi pol ρ (.app t (payload a b))

theorem app_head_dominates  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b s t : OriginalTerm Γ unary) (hst : value1 Phi pol ρ s<value1 Phi pol ρ t)
    (hs : value0 Phi pol ρ s≤groundValue Phi pol ρ (payload a b)) :
    4*observedApp Phi pol ρ a b s<observedApp Phi pol ρ a b t := by
  unfold observedApp
  rw [unaryApp  pol,unaryApp  pol]
  exact app_strict_head  _ _ _ _ _ (values_facts  pol ρ s).2.1
    (values_facts  pol ρ s).2.2.1 (values_facts  pol ρ t).2.2.1 hst
    (values_facts  pol ρ s).2.2.2 hs (payload_five  pol ρ a b)

theorem app_tail_dominates  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b s t : OriginalTerm Γ unary) (hh : value1 Phi pol ρ s=value1 Phi pol ρ t)
    (hs : value0 Phi pol ρ s+2≤value0 Phi pol ρ t) :
    4*observedApp Phi pol ρ a b s<observedApp Phi pol ρ a b t := by
  unfold observedApp
  rw [unaryApp  pol,unaryApp  pol]
  unfold appValue
  rw [hh]
  exact tail_gap_fourfold  _ (omega_product_below _ (values_facts  pol ρ t).2.2.1)
    (omega_product_limit _ (values_facts  pol ρ t).2.1 (values_facts  pol ρ t).2.2.1) _ _ _ hs

theorem combine_scalar_gap  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b c d : OriginalTerm Γ unary)
    (hh : headCombine (value1 Phi pol ρ a) (value1 Phi pol ρ b)=headCombine (value1 Phi pol ρ c) (value1 Phi pol ρ d))
    (ht : 9*value0 Phi pol ρ a+5*value0 Phi pol ρ b+13+2≤9*value0 Phi pol ρ c+5*value0 Phi pol ρ d+13) :
    value0 Phi pol ρ (combine a b)+2≤value0 Phi pol ρ (combine c d) := by
  rw [combine_scalar  pol,combine_scalar  pol,hh]
  apply collapse_gap_two  _ _ _ _ ht
  apply omega_product_below
  rw [← combine_head  pol]
  exact (values_facts  pol ρ (combine c d)).2.2.1

theorem headCombine_comm (a b : Ordinal) : headCombine a b=headCombine b a := by
  unfold headCombine
  rw [sum_comm (paddedHead a) (paddedHead b)]

theorem observed_equal  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b s t : OriginalTerm Γ unary)
    (h0 : value0 Phi pol ρ s=value0 Phi pol ρ t) (h1 : value1 Phi pol ρ s=value1 Phi pol ρ t) :
    observedApp Phi pol ρ a b s=observedApp Phi pol ρ a b t := by
  unfold observedApp
  rw [unaryApp  pol,unaryApp  pol,h0,h1]

theorem left_value  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    groundValue Phi pol ρ (left a b)=
      ParametricActualCollapse.collapseWith Phi (Ordinal.omega0 + ((3*observedApp Phi pol ρ a b (combine a a)+observedApp Phi pol ρ a b (combine b b)+2 : Nat) : Ordinal)) :=
  eraser_value  pol ρ _ _

theorem right_value  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    groundValue Phi pol ρ (right a b)=
      ParametricActualCollapse.collapseWith Phi (Ordinal.omega0 + ((3*observedApp Phi pol ρ a b (combine a b)+observedApp Phi pol ρ a b (combine b a)+2 : Nat) : Ordinal)) :=
  eraser_value  pol ρ _ _
end LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
