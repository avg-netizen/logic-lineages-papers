module
public import LogicLineages.PermittedControl.SelectedDetectorComparisonProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain
open Source.FunctionalDetector (unary combine left right)
open SelectedHardness (value0 value1)
open Source.FunctionalDetector.Proof (headCombine_strict_left twice_le_pow)

theorem eraser_gap (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (s t : Nat) (hst : s<t) :
    ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0+(s : Ordinal))+2 ≤
      ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0+(t : Ordinal)) := by
  have he := SelectedValueClosureProof.omega_below
  have h1 := fixedHeadTailGrowth ctrl K hc Ordinal.omega0 he Ordinal.isSuccLimit_omega0 s
  have h2 := finite_tail_gap ctrl K hc Ordinal.omega0 he (s+1) t (by omega)
  have hp := collapse_nonfinite ctrl (selected_threshold_admissible ctrl K hc).2
    (Ordinal.omega0+(s : Ordinal)) (actualFiniteTailClosureNorm Ordinal.omega0 he s).1 le_self_add
  have hb := twice_le_pow (ParametricActualCollapse.collapseWith ctrl (Ordinal.omega0+(s : Ordinal)))
  omega

theorem equal_detector (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ unary) (h : VectorEqual ctrl pol ρ a b) :
    groundValue ctrl pol ρ (left a b)=groundValue ctrl pol ρ (right a b) := by
  obtain ⟨h0,h1⟩ := (vector_equal_values ctrl K hc pol ρ a b).mp h
  have hx : observedApp ctrl pol ρ a b (combine a a)=observedApp ctrl pol ρ a b (combine a b) := by
    apply observed_equal ctrl K hc pol
    · simp only [(combine_scalar ctrl K hc pol),h0,h1]
    · simp only [(combine_head ctrl K hc pol),h1]
  have hy : observedApp ctrl pol ρ a b (combine b b)=observedApp ctrl pol ρ a b (combine b a) := by
    apply observed_equal ctrl K hc pol
    · simp only [(combine_scalar ctrl K hc pol),h0,h1]
    · simp only [(combine_head ctrl K hc pol),h1]
  rw [(left_value ctrl K hc pol),(right_value ctrl K hc pol),hx,hy]

theorem scalar_diagonal_domination (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ unary) (hh : value1 ctrl pol ρ a=value1 ctrl pol ρ b)
    (hne : value0 ctrl pol ρ a≠value0 ctrl pol ρ b) :
    (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine a a) ∧
      4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine a a)) ∨
    (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine b b) ∧
      4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine b b)) := by
  by_cases hlt : value0 ctrl pol ρ b<value0 ctrl pol ρ a
  · left
    constructor
    · apply app_tail_dominates ctrl K hc pol
      · simp only [(combine_head ctrl K hc pol),hh]
      · apply combine_scalar_gap ctrl K hc pol
        · simp only [hh]
        · omega
    · apply app_tail_dominates ctrl K hc pol
      · simp only [(combine_head ctrl K hc pol),hh]
      · apply combine_scalar_gap ctrl K hc pol
        · simp only [hh]
        · omega
  · right
    have hgt : value0 ctrl pol ρ a<value0 ctrl pol ρ b := by omega
    constructor
    · apply app_tail_dominates ctrl K hc pol
      · simp only [(combine_head ctrl K hc pol),hh]
      · apply combine_scalar_gap ctrl K hc pol
        · simp only [hh]
        · omega
    · apply app_tail_dominates ctrl K hc pol
      · simp only [(combine_head ctrl K hc pol),hh]
      · apply combine_scalar_gap ctrl K hc pol
        · simp only [hh]
        · omega
theorem head_diagonal_domination (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ)
    (a b : OriginalTerm Γ unary) (hne : value1 ctrl pol ρ a≠value1 ctrl pol ρ b) :
    (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine a a) ∧
     4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine a a)) ∨
    (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine b b) ∧
     4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine b b)) := by
  have hz := (payload_components ctrl K hc pol ρ a b).2.2.1
  have hw := (payload_components ctrl K hc pol ρ a b).2.2.2
  have hmono (u v w : OriginalTerm Γ unary) (huv : value1 ctrl pol ρ u<value1 ctrl pol ρ v) :
      value1 ctrl pol ρ (combine u w)<value1 ctrl pol ρ (combine v w) := by
    rw [(combine_head ctrl K hc pol),(combine_head ctrl K hc pol)]
    exact headCombine_strict_left (value1 ctrl pol ρ u) (value1 ctrl pol ρ v) (value1 ctrl pol ρ w)
      (values_facts ctrl K hc pol ρ u).2.2.1 (values_facts ctrl K hc pol ρ v).2.2.1 (values_facts ctrl K hc pol ρ w).2.2.1 huv
  have hs (u v : OriginalTerm Γ unary) : value1 ctrl pol ρ (combine u v)=value1 ctrl pol ρ (combine v u) := by
    rw [(combine_head ctrl K hc pol),(combine_head ctrl K hc pol),headCombine_comm]
  rcases lt_or_gt_of_ne hne with hab | hba
  · right
    exact ⟨app_head_dominates ctrl K hc pol ρ a b _ _ (hmono a b b hab) hz,
      app_head_dominates ctrl K hc pol ρ a b _ _ (by rw [hs b a]; exact hmono a b b hab) hw⟩
  · left
    exact ⟨app_head_dominates ctrl K hc pol ρ a b _ _ (by rw [hs a b]; exact hmono b a a hba) hz,
      app_head_dominates ctrl K hc pol ρ a b _ _ (hmono b a a hba) hw⟩

theorem unequal_strict (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) {Γ} (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary)
    (hne : ¬VectorEqual ctrl pol ρ a b) :
    groundValue ctrl pol ρ (right a b)+2≤groundValue ctrl pol ρ (left a b) := by
  have hd :
      (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine a a) ∧
       4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine a a)) ∨
      (4*observedApp ctrl pol ρ a b (combine a b)<observedApp ctrl pol ρ a b (combine b b) ∧
       4*observedApp ctrl pol ρ a b (combine b a)<observedApp ctrl pol ρ a b (combine b b)) := by
    by_cases hh : value1 ctrl pol ρ a=value1 ctrl pol ρ b
    · have hn : value0 ctrl pol ρ a≠value0 ctrl pol ρ b := by
        intro h
        exact hne ((vector_equal_values ctrl K hc pol ρ a b).mpr ⟨h,hh⟩)
      exact scalar_diagonal_domination ctrl K hc pol ρ a b hh hn
    · exact head_diagonal_domination ctrl K hc pol ρ a b hh
  have hi : 3*observedApp ctrl pol ρ a b (combine a b)+observedApp ctrl pol ρ a b (combine b a)+2 <
      3*observedApp ctrl pol ρ a b (combine a a)+observedApp ctrl pol ρ a b (combine b b)+2 := by
    rcases hd with hd | hd <;> omega
  rw [(right_value ctrl K hc pol),(left_value ctrl K hc pol)]
  exact eraser_gap ctrl K hc _ _ hi

theorem detector {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (pol : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (a b : OriginalTerm Γ unary) :
    Detects ctrl pol ρ a b := by
  obtain ⟨lv,hl,hlv,hlp⟩ := ground_facts ctrl K hc pol (left a b) ρ
  obtain ⟨rv,hr,hrv,hrp⟩ := ground_facts ctrl K hc pol (right a b) ρ
  refine ⟨⟨lv,rv,hl,hr,hlv,hrv⟩,?_⟩
  by_cases he : VectorEqual ctrl pol ρ a b
  · have hv := equal_detector ctrl K hc pol ρ a b he
    exact ⟨hv.ge,⟨fun _ => he,fun _ => hv⟩,fun h => False.elim (h he)⟩
  · have hs := unequal_strict ctrl K hc pol ρ a b he
    exact ⟨by omega,⟨fun h => by omega,fun h => False.elim (he h)⟩,fun _ => hs⟩

theorem fullSelectedFunctionalDetector : SelectedFunctionalDetectorTargets.FullSelectedFunctionalDetector := by
  refine ⟨positiveValue,?_⟩
  intro ctrl K hc Γ pol a b ρ
  exact ⟨alignment ctrl K hc pol Γ a b ρ,detector ctrl K hc pol ρ a b⟩
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
