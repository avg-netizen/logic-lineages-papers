module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumArithmeticProof
public import LogicLineages.OrdinalComparison.ControlResidueProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueProof
open BlockRows PlainMaximum PlainMaximumResidue

private theorem lower_value (m i : Nat) (r : Row) (ν : Nat → Nat) :
    rowValue (lowerRow m i r) ν = constantValue r ν +
      headCoefficient i r * (fastControlResidue (m + 1) : Int) + remainderValue i r ν := by
  have hc : ((headCoefficient i r).toNat : Int) -
      ((-(headCoefficient i r)).toNat : Int) = headCoefficient i r := by omega
  calc
    rowValue (lowerRow m i r) ν = constantValue r ν +
        (((headCoefficient i r).toNat : Int) - ((-(headCoefficient i r)).toNat : Int)) *
          (fastControlResidue (m + 1) : Int) + remainderValue i r ν := by
      simp only [lowerRow, rowValue, constantValue, remainderValue,
        Term.value, Int.natCast_add, Int.natCast_mul]
      ring
    _ = _ := by rw [hc]

theorem actualOriginalTailCalibration : PlainMaximumResidueTargets.ActualOriginalTailCalibration := by
  intro m i r ν hcut
  have hres := phiShiftedConstantResidues (m + 1) (by omega) (ν i) hcut
  obtain ⟨z, hz⟩ := hres.dvd
  have hdiff : rowValue (lowerRow m i r) ν = rowValue r ν + headCoefficient i r *
      ((fastControlResidue (m + 1) : Int) - (Phi (ν i) : Int)) := by
    rw [lower_value, PlainMaximumProof.exactOriginalHeadDecomposition r i ν]
    ring
  change (((m + 1 : Nat) : Int) ∣ rowValue (lowerRow m i r) ν) ↔
    (((m + 1 : Nat) : Int) ∣ rowValue r ν)
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w - headCoefficient i r * z, ?_⟩
    calc
      rowValue r ν = rowValue (lowerRow m i r) ν - headCoefficient i r *
          ((fastControlResidue (m + 1) : Int) - (Phi (ν i) : Int)) := by rw [hdiff]; ring
      _ = ((m + 1 : Nat) : Int) * w - headCoefficient i r * (((m + 1 : Nat) : Int) * z) := by
        rw [hw, hz]
      _ = _ := by ring
  · rintro ⟨w, hw⟩
    refine ⟨w + headCoefficient i r * z, ?_⟩
    rw [hdiff, hw, hz]
    ring

theorem literalRemainingOccurrences : PlainMaximumResidueTargets.LiteralRemainingOccurrences := by
  intro m i r
  rfl

private theorem parameter_support (m i : Nat) (r : Row) (j : Nat) :
    j ∈ (lowerAtom m i r).parameters ↔ j ∈ r.parameters := by
  simp [lowerAtom, lowerRow, Formula.parameters, Atom.row, Row.parameters, Term.variables]

private theorem remaining_linear (bound : List Nat) (r : Row) (i : Nat)
    (hallowed : PlainMaximum.allowed bound r = true) :
    (remainingOccurrences i r).all (fun a => linearSummand i a.2) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨ha, hh⟩ := List.mem_filter.mp ha
  have hall := List.all_eq_true.mp hallowed a ha
  have hn : isHead i a.2 = false := by simpa using hh
  cases hs : a.2 with
  | «variable» j => rfl
  | phi j shift =>
    have hphi : j ∈ bound ∧ shift = 0 := by simpa [allowedSummand, hs] using hall
    rcases hphi with ⟨_, rfl⟩
    have hji : j ≠ i := by intro h; subst j; simp [hs, isHead] at hn
    simpa [hs, linearSummand] using hji
  | hyperPhi j e h => simp [hs, allowedSummand] at hall

theorem exactEliminandLinearity : PlainMaximumResidueTargets.ExactEliminandLinearity := by
  intro bound r m i hallowed hiparams
  have hp : i ∉ (lowerAtom m i r).parameters := by
    simpa only [parameter_support] using hiparams
  have htest : (!(lowerAtom m i r).parameters.contains i) = true := by simpa using hp
  unfold linearIn
  rw [htest, Bool.true_and]
  exact remaining_linear bound r i hallowed

theorem wholeBlockParameterPreservation : PlainMaximumResidueTargets.WholeBlockParameterPreservation := by
  intro bound r m i hparams j hj hnew
  exact hparams j hj ((parameter_support m i r j).mp hnew)

theorem originalNameSupport : PlainMaximumResidueTargets.OriginalNameSupport := by
  intro m i r j hj
  change j ∈ (lowerRow m i r).variables at hj
  simp only [lowerRow, Row.variables, Term.variables, List.mem_append,
    List.not_mem_nil, or_false] at hj
  rcases hj with hparams | ho
  · simp only [Row.variables, List.mem_append]
    exact Or.inl hparams
  · obtain ⟨a, ha, hname⟩ := List.mem_map.mp ho
    simp only [Row.variables, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨a, (List.mem_filter.mp ha).1, hname⟩)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueProof
