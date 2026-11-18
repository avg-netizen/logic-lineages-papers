module
public import LogicLineages.PermittedControl.StandardDetectorComparisonProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open Source.FunctionalDetector (unary combine left right)
open SelectedHardness (value0 value1)
open Source.FunctionalDetector.Proof (headCombine_strict_left twice_le_pow)

theorem eraser_gap (s t : Nat) (hst : s<t) :
    ParametricActualCollapse.collapseWith Phi (Ordinal.omega0+(s : Ordinal))+2 ≤
      ParametricActualCollapse.collapseWith Phi (Ordinal.omega0+(t : Ordinal)) := by
  have he := SelectedValueClosureProof.omega_below
  have h1 := (actualTailSeparation Ordinal.omega0 he Ordinal.isSuccLimit_omega0).1 s
  simp only [← ParametricSourceSuccessor.Proof.phi_global] at h1
  have h2 := finite_tail_gap Ordinal.omega0 he (s+1) t (by omega)
  have hp := collapse_nonfinite Phi (fun _ => le_rfl)
    (Ordinal.omega0+(s : Ordinal)) (actualFiniteTailClosureNorm Ordinal.omega0 he s).1 le_self_add
  have hb := twice_le_pow (ParametricActualCollapse.collapseWith Phi (Ordinal.omega0+(s : Ordinal)))
  omega
theorem equal_detector  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ unary) (h : VectorEqual Phi pol ρ a b) :
    groundValue Phi pol ρ (left a b)=groundValue Phi pol ρ (right a b) := by
  obtain ⟨h0,h1⟩ := (vector_equal_values  pol ρ a b).mp h
  have hx : observedApp Phi pol ρ a b (combine a a)=observedApp Phi pol ρ a b (combine a b) := by
    apply observed_equal  pol
    · simp only [(combine_scalar  pol),h0,h1]
    · simp only [(combine_head  pol),h1]
  have hy : observedApp Phi pol ρ a b (combine b b)=observedApp Phi pol ρ a b (combine b a) := by
    apply observed_equal  pol
    · simp only [(combine_scalar  pol),h0,h1]
    · simp only [(combine_head  pol),h1]
  rw [(left_value  pol),(right_value  pol),hx,hy]

theorem scalar_diagonal_domination  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ unary) (hh : value1 Phi pol ρ a=value1 Phi pol ρ b)
    (hne : value0 Phi pol ρ a≠value0 Phi pol ρ b) :
    (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine a a) ∧
      4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine a a)) ∨
    (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine b b) ∧
      4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine b b)) := by
  by_cases hlt : value0 Phi pol ρ b<value0 Phi pol ρ a
  · left
    constructor
    · apply app_tail_dominates  pol
      · simp only [(combine_head  pol),hh]
      · apply combine_scalar_gap  pol
        · simp only [hh]
        · omega
    · apply app_tail_dominates  pol
      · simp only [(combine_head  pol),hh]
      · apply combine_scalar_gap  pol
        · simp only [hh]
        · omega
  · right
    have hgt : value0 Phi pol ρ a<value0 Phi pol ρ b := by omega
    constructor
    · apply app_tail_dominates  pol
      · simp only [(combine_head  pol),hh]
      · apply combine_scalar_gap  pol
        · simp only [hh]
        · omega
    · apply app_tail_dominates  pol
      · simp only [(combine_head  pol),hh]
      · apply combine_scalar_gap  pol
        · simp only [hh]
        · omega
theorem head_diagonal_domination  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ)
    (a b : OriginalTerm Γ unary) (hne : value1 Phi pol ρ a≠value1 Phi pol ρ b) :
    (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine a a) ∧
     4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine a a)) ∨
    (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine b b) ∧
     4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine b b)) := by
  have hz := (payload_components  pol ρ a b).2.2.1
  have hw := (payload_components  pol ρ a b).2.2.2
  have hmono (u v w : OriginalTerm Γ unary) (huv : value1 Phi pol ρ u<value1 Phi pol ρ v) :
      value1 Phi pol ρ (combine u w)<value1 Phi pol ρ (combine v w) := by
    rw [(combine_head  pol),(combine_head  pol)]
    exact headCombine_strict_left (value1 Phi pol ρ u) (value1 Phi pol ρ v) (value1 Phi pol ρ w)
      (values_facts  pol ρ u).2.2.1 (values_facts  pol ρ v).2.2.1 (values_facts  pol ρ w).2.2.1 huv
  have hs (u v : OriginalTerm Γ unary) : value1 Phi pol ρ (combine u v)=value1 Phi pol ρ (combine v u) := by
    rw [(combine_head  pol),(combine_head  pol),headCombine_comm]
  rcases lt_or_gt_of_ne hne with hab | hba
  · right
    exact ⟨app_head_dominates  pol ρ a b _ _ (hmono a b b hab) hz,
      app_head_dominates  pol ρ a b _ _ (by rw [hs b a]; exact hmono a b b hab) hw⟩
  · left
    exact ⟨app_head_dominates  pol ρ a b _ _ (by rw [hs a b]; exact hmono b a a hba) hz,
      app_head_dominates  pol ρ a b _ _ (hmono b a a hba) hw⟩

theorem unequal_strict  (pol : Policy) {Γ} (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary)
    (hne : ¬VectorEqual Phi pol ρ a b) :
    groundValue Phi pol ρ (right a b)+2≤groundValue Phi pol ρ (left a b) := by
  have hd :
      (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine a a) ∧
       4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine a a)) ∨
      (4*observedApp Phi pol ρ a b (combine a b)<observedApp Phi pol ρ a b (combine b b) ∧
       4*observedApp Phi pol ρ a b (combine b a)<observedApp Phi pol ρ a b (combine b b)) := by
    by_cases hh : value1 Phi pol ρ a=value1 Phi pol ρ b
    · have hn : value0 Phi pol ρ a≠value0 Phi pol ρ b := by
        intro h
        exact hne ((vector_equal_values  pol ρ a b).mpr ⟨h,hh⟩)
      exact scalar_diagonal_domination  pol ρ a b hh hn
    · exact head_diagonal_domination  pol ρ a b hh
  have hi : 3*observedApp Phi pol ρ a b (combine a b)+observedApp Phi pol ρ a b (combine b a)+2 <
      3*observedApp Phi pol ρ a b (combine a a)+observedApp Phi pol ρ a b (combine b b)+2 := by
    rcases hd with hd | hd <;> omega
  rw [(right_value  pol),(left_value  pol)]
  exact eraser_gap  _ _ hi

theorem detector {Γ} 
    (pol : Policy) (ρ : AdmissibleSubstitution Phi Γ) (a b : OriginalTerm Γ unary) :
    Detects Phi pol ρ a b := by
  obtain ⟨lv,hl,hlv,hlp⟩ := ground_facts  pol (left a b) ρ
  obtain ⟨rv,hr,hrv,hrp⟩ := ground_facts  pol (right a b) ρ
  refine ⟨⟨lv,rv,hl,hr,hlv,hrv⟩,?_⟩
  by_cases he : VectorEqual Phi pol ρ a b
  · have hv := equal_detector  pol ρ a b he
    exact ⟨hv.ge,⟨fun _ => he,fun _ => hv⟩,fun h => False.elim (h he)⟩
  · have hs := unequal_strict  pol ρ a b he
    exact ⟨by omega,⟨fun h => by omega,fun h => False.elim (he h)⟩,fun _ => hs⟩


theorem standardFunctionalDetector : StandardFunctionalDetector := by
  refine ⟨extensionCalibration,?_,?_⟩
  · intro Γ pol a b ρ
    exact alignment pol Γ a b ρ
  · intro Γ pol a b ρ
    obtain ⟨lv,hl,hls,hlp⟩ := ground_facts pol (left a b) ρ
    obtain ⟨rv,hr,hrs,hrp⟩ := ground_facts pol (right a b) ρ
    exact ⟨detector pol ρ a b,hlp,hrp⟩
end LogicLineages.PermittedControl.StandardFunctionalDetector.Proof
