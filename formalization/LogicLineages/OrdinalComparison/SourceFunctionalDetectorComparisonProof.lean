module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlignmentProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorValuesProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorPayloadProof
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain AdmissibleAssignment
open SourceCollisionCompletion (rawScalar g)

theorem vector_equal_values {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    VectorEqual ρ a b ↔ value0 ρ a=value0 ρ b ∧ value1 ρ a=value1 ρ b := by
  obtain ⟨av,ha,ha0,ha1⟩ := values_assignment ρ a
  obtain ⟨bv,hb,hb0,hb1⟩ := values_assignment ρ b
  rw [vectorEqual_iff ρ a b av bv ha hb]
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

noncomputable def observedApp {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b t : OriginalTerm Γ unary) : Nat := rawScalar (valuation ρ) (.app t (payload a b))

theorem app_head_dominates {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b s t : OriginalTerm Γ unary) (hst : value1 ρ s<value1 ρ t)
    (hs : value0 ρ s≤rawScalar (valuation ρ) (payload a b)) :
    4*observedApp ρ a b s<observedApp ρ a b t := by
  unfold observedApp
  rw [unaryApp,unaryApp]
  exact app_strict_head _ _ _ _ _ (values_facts ρ s).2.1
    (values_facts ρ s).2.2.1 (values_facts ρ t).2.2.1 hst
    (values_facts ρ s).2.2.2 hs (payload_five ρ a b)

theorem app_tail_dominates {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b s t : OriginalTerm Γ unary) (hh : value1 ρ s=value1 ρ t)
    (hs : value0 ρ s+2≤value0 ρ t) :
    4*observedApp ρ a b s<observedApp ρ a b t := by
  unfold observedApp
  rw [unaryApp,unaryApp]
  unfold appValue
  rw [hh]
  exact tail_gap_fourfold _ (omega_product_below _ (values_facts ρ t).2.2.1)
    (omega_product_limit _ (values_facts ρ t).2.1 (values_facts ρ t).2.2.1) _ _ _ hs

theorem collapse_gap_two (h : Ordinal) (he : h<epsilonZero) (s t : Nat) (hst : s+2≤t) :
    actualCollapse (h+(s:Ordinal))+2≤actualCollapse (h+(t:Ordinal)) := by
  have hi := actualCollapseFiniteTailIncrement (h+(s:Ordinal))
    (actualFiniteTailClosureNorm h he s).1 2
  have hh : h+(s:Ordinal)+(2:Ordinal)=h+((s+2:Nat):Ordinal) := by
    rw [Nat.cast_add,add_assoc]
    rfl
  change actualCollapse (h+(s:Ordinal))+2≤actualCollapse (h+(s:Ordinal)+(2:Ordinal)) at hi
  rw [hh] at hi
  exact hi.trans (actualCollapseFiniteTailMonotone h he _ _ hst)

theorem combine_scalar_gap {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b c d : OriginalTerm Γ unary)
    (hh : headCombine (value1 ρ a) (value1 ρ b)=headCombine (value1 ρ c) (value1 ρ d))
    (ht : 9*value0 ρ a+5*value0 ρ b+13+2≤9*value0 ρ c+5*value0 ρ d+13) :
    value0 ρ (combine a b)+2≤value0 ρ (combine c d) := by
  rw [combine_scalar,combine_scalar,hh]
  apply collapse_gap_two _ _ _ _ ht
  apply omega_product_below
  rw [← combine_head]
  exact (values_facts ρ (combine c d)).2.2.1

theorem headCombine_comm (a b : Ordinal) : headCombine a b=headCombine b a := by
  unfold headCombine
  rw [sum_comm (paddedHead a) (paddedHead b)]

theorem observed_equal {Γ} (ρ : AdmissibleSubstitution Γ)
    (a b s t : OriginalTerm Γ unary)
    (h0 : value0 ρ s=value0 ρ t) (h1 : value1 ρ s=value1 ρ t) :
    observedApp ρ a b s=observedApp ρ a b t := by
  unfold observedApp
  rw [unaryApp,unaryApp,h0,h1]

theorem left_value {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    rawScalar (valuation ρ) (left a b)=
      g (3*observedApp ρ a b (combine a a)+observedApp ρ a b (combine b b)+2) :=
  SourceCollisionCompletion.Proof.actualGroundEraser Γ _ _ ρ

theorem right_value {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary) :
    rawScalar (valuation ρ) (right a b)=
      g (3*observedApp ρ a b (combine a b)+observedApp ρ a b (combine b a)+2) :=
  SourceCollisionCompletion.Proof.actualGroundEraser Γ _ _ ρ
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
