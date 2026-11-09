module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitWitnessProof
public import Mathlib.Data.Finset.Max
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem small_in_branches (bound : List Nat) (p : Formula) (s : State) (hs : s ∈ small bound p) :
    s ∈ branches bound p :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hs))
theorem ties_in_branches (bound : List Nat) (p : Formula) (s : State) (hs : s ∈ ties bound p) :
    s ∈ branches bound p :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
theorem bands_in_branches (bound : List Nat) (p : Formula) (s : State) (hs : s ∈ bands bound p) :
    s ∈ branches bound p := List.mem_append_left _ (List.mem_append_right _ hs)
theorem far_in_branches (bound : List Nat) (p : Formula) (s : State) (hs : s ∈ far bound p) :
    s ∈ branches bound p := List.mem_append_right _ hs

theorem branch_sound (bound : List Nat) (p : Formula) (s : State) (ν : Nat → Nat)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p)
    (hs : s ∈ branches bound p) (hp : existsPrefix ν s.1 s.2) : existsPrefix ν bound p := by
  change s ∈ ((small bound p ++ ties bound p) ++ bands bound p) ++ far bound p at hs
  rcases List.mem_append.mp hs with hleft | hfar
  · rcases List.mem_append.mp hleft with hleft | hbands
    · rcases List.mem_append.mp hleft with hsmall | hties
      · cases bound with
        | nil => simp [small] at hsmall
        | cons i rest =>
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hsmall
          exact substitution_sound (i :: rest) p i (.numeral n) ν List.mem_cons_self hp
      · obtain ⟨i, hi, hinner⟩ := List.mem_flatMap.mp hties
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hinner
        exact tie_sound bound p i j ν hi (hparams i hi) hp
    · obtain ⟨i, hi, hinner⟩ := List.mem_flatMap.mp hbands
      obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hinner
      cases a with
      | nonnegative r =>
        change s ∈ (if PlainMaximum.headCoefficient i r = 0 then [] else
          (List.range 5).map (fun d =>
            (bound.erase i, p.substitute i (bandCandidate i r d)))) at ha
        by_cases hz : PlainMaximum.headCoefficient i r = 0
        · simp only [if_pos hz, List.not_mem_nil] at ha
        · rw [if_neg hz] at ha
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
          exact substitution_sound bound p i (bandCandidate i r d) ν hi hp
      | divisible m r => exact False.elim (List.not_mem_nil ha)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hfar
    exact far_sound bound p i ν hi hallowed hparams hp

theorem band_candidate_omits (bound : List Nat) (p : Formula) (i : Nat) (r : Row) (d : Nat)
    (hi : i ∈ bound) (hparams : ParametersIndependent bound p)
    (hr : Atom.nonnegative r ∈ atoms p) : i ∉ (bandCandidate i r d).variables := by
  have hrow : i ∉ r.parameters := fun h => hparams i hi (atom_parameter_support p (.nonnegative r) hr i h)
  have hc : i ∉ (PlainMaximum.boundary i r).variables := by
    simpa only [PlainMaximumProof.boundary_support] using hrow
  simpa only [bandCandidate, Term.variables, List.mem_append, List.not_mem_nil, or_false] using hc

theorem outside_from_no_band (i : Nat) (p : Formula) (σ : Nat → Nat)
    (hband : ¬∃ r, Atom.nonnegative r ∈ atoms p ∧ PlainMaximum.headCoefficient i r ≠ 0 ∧
      ¬PlainMaximum.OutsideBoundary i r σ) : (outside i p).eval σ := by
  apply (all_eval _ σ).mpr
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  cases a with
  | nonnegative r =>
    apply (outside_row_eval i r σ).mpr
    by_cases hz : PlainMaximum.headCoefficient i r = 0
    · exact Or.inl hz
    · by_contra hout
      exact hband ⟨r, ha, hz, hout⟩
  | divisible m r => trivial

private theorem success_of_state (bound : List Nat) (p : Formula) (remaining : List Nat)
    (q : Formula) (ν : Nat → Nat) (hmem : (remaining, q) ∈ branches bound p)
    (hpref : existsPrefix ν remaining q) :
    ∃ s ∈ branches bound p, existsPrefix ν s.1 s.2 :=
  ⟨(remaining, q), hmem, hpref⟩

private theorem far_success (bound : List Nat) (p : Formula) (i : Nat) (ν σ : Nat → Nat)
    (hi : i ∈ bound) (hallowed : TiedLinear.allowed bound p = true)
    (hparams : ParametersIndependent bound p)
    (hσ : ∀ j, j ∉ bound → σ j = ν j) (hp : p.eval σ)
    (hframe : (frame bound i p).eval σ) (hout : (outside i p).eval σ) :
    ∃ s ∈ branches bound p, existsPrefix ν s.1 s.2 :=
  success_of_state bound p (bound.erase i)
    (TiedLinear.eliminate i
      (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))) ν
    (far_in_branches bound p _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
    (far_complete bound p i ν σ hi hallowed hparams hσ hp hframe hout)

theorem actualOneStepProjection : PlainBlockSplitTargets.ActualOneStepProjection := by
  classical
  intro bound p _ hnonempty hallowed hparams ν
  constructor
  · intro hpref
    obtain ⟨σ, hσ, hp⟩ := (existsPrefix_iff_frame ν bound p).mp hpref
    by_cases hsmall : ∀ i ∈ bound, σ i < cutoff p
    · cases bound with
      | nil => exact False.elim (hnonempty rfl)
      | cons i rest =>
        refine ⟨((i :: rest).erase i, p.substitute i (.numeral (σ i))), ?_, ?_⟩
        · apply small_in_branches
          exact List.mem_map.mpr ⟨σ i, List.mem_range.mpr (hsmall i List.mem_cons_self), rfl⟩
        · exact substitution_complete (i :: rest) p i (.numeral (σ i)) ν σ hσ hp
            (by simp [Term.variables]) rfl
    · push Not at hsmall
      obtain ⟨j, hj, hlarge⟩ := hsmall
      have hne : bound.toFinset.Nonempty := ⟨j, List.mem_toFinset.mpr hj⟩
      obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image bound.toFinset σ hne
      have hib : i ∈ bound := List.mem_toFinset.mp hi
      have hcut : cutoff p ≤ σ i := hlarge.trans (hmax j (List.mem_toFinset.mpr hj))
      by_cases htie : ∃ j ∈ bound, j ≠ i ∧ σ j = σ i
      · obtain ⟨j, hj, hji, heq⟩ := htie
        refine ⟨(bound.erase i, rename i j p), ?_, ?_⟩
        · apply ties_in_branches
          apply List.mem_flatMap.mpr
          refine ⟨i, hib, List.mem_map.mpr ⟨j, ?_, rfl⟩⟩
          exact List.mem_filter.mpr ⟨hj, by simpa using hji⟩
        · exact tie_complete bound p i j ν σ hσ hp (hparams i hib) hji heq
      · have hUnique : PlainMaximum.UniqueMaximum bound i σ := by
          refine ⟨hib, ?_⟩
          intro j hj hji
          have hjle := hmax j (List.mem_toFinset.mpr hj)
          have hneq : σ j ≠ σ i := fun he => htie ⟨j, hj, hji, he⟩
          omega
        by_cases hband : ∃ r, Atom.nonnegative r ∈ atoms p ∧ PlainMaximum.headCoefficient i r ≠ 0 ∧
            ¬PlainMaximum.OutsideBoundary i r σ
        · obtain ⟨r, hr, hcoef, hout⟩ := hband
          let c := (PlainMaximum.boundary i r).value σ
          have hlo : c - 2 ≤ σ i := by
            by_contra h
            apply hout
            exact Or.inr (Or.inl (by omega))
          have hhi : σ i ≤ c + 2 := by
            by_contra h
            apply hout
            exact Or.inr (Or.inr (by omega))
          let d := σ i - (c - 2)
          have hd : d < 5 := by dsimp only [d]; omega
          have hvalue : (bandCandidate i r d).value σ = σ i := by
            change c - 2 + d = σ i
            dsimp only [d]
            omega
          refine ⟨(bound.erase i, p.substitute i (bandCandidate i r d)), ?_, ?_⟩
          · apply bands_in_branches
            apply List.mem_flatMap.mpr
            refine ⟨i, hib, List.mem_flatMap.mpr ⟨.nonnegative r, hr, ?_⟩⟩
            change _ ∈ (if PlainMaximum.headCoefficient i r = 0 then [] else _)
            rw [if_neg hcoef]
            exact List.mem_map.mpr ⟨d, List.mem_range.mpr hd, rfl⟩
          · exact substitution_complete bound p i (bandCandidate i r d) ν σ hσ hp
              (band_candidate_omits bound p i r d hib hparams hr) hvalue
        · have hframe : (frame bound i p).eval σ := (frame_eval bound i p σ).mpr ⟨hcut, hUnique.2⟩
          have hout := outside_from_no_band i p σ hband
          exact far_success bound p i ν σ hib hallowed hparams hσ hp hframe hout
  · rintro ⟨s, hs, hp⟩
    exact branch_sound bound p s ν hallowed hparams hs hp

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
