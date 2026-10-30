module
public import LogicLineages.OrdinalComparison.LinkedCartierCycleTargets
public import LogicLineages.OrdinalComparison.BinaryCartierExtensionProof
public import LogicLineages.OrdinalComparison.BinaryCartierCycleProof
public import LogicLineages.OrdinalComparison.LinkedResidueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualLinkedCartierInitialProper : Targets.ActualLinkedCartierInitialProper := by
  intro u hu
  obtain ⟨_, _, _, _, _, _, _, hqd, _, hmq, _⟩ :=
    actualLinkedResidueArithmetic u (by omega)
  have htd : actualLinkedTail u < actualLinkedCutoff u := hmq.trans_le hqd
  have hed : actualLinkedOffset u - 1 < actualLinkedCutoff u := by
    unfold actualLinkedOffset actualLinkedTail at *
    omega
  have hd : 0 < actualLinkedCutoff u := Nat.zero_le _ |>.trans_lt hed
  have hdD : actualLinkedCutoff u ≤ actualBinarySourceDimension (actualLinkedCutoff u) := by
    unfold actualBinarySourceDimension
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    nlinarith
  rw [Polynomial.degree_X_pow]
  exact Nat.cast_lt.mpr (hed.trans_le hdD)

private theorem extension_iterate (f : RatFunc (ZMod 2)) (j : Nat) :
    actualBinaryRationalExtension ActualResidueField ((actualDifferentialCartier^[j]) f) =
      (actualDifferentialCartier^[j]) (actualBinaryRationalExtension ActualResidueField f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', actualBinaryRationalExtensionCartier,
      ih, Function.iterate_succ_apply']

theorem actualSourceCartierEventualCycle : Targets.ActualSourceCartierEventualCycle := by
  intro v hv
  have hu : 5 ≤ Phi v := by have := self_lt_Phi v; omega
  let U : ActualBinaryProperNumerator (actualLinkedCutoff (Phi v)) :=
    ⟨Polynomial.X ^ (actualLinkedOffset (Phi v) - 1), actualLinkedCartierInitialProper _ hu⟩
  obtain ⟨j, p, hp, h⟩ := actualBinaryCartierEventualCycle _ U
  refine ⟨j, p, hp, ?_⟩
  intro k
  have he := congrArg (actualBinaryRationalExtension ActualResidueField) (h k)
  rw [extension_iterate, extension_iterate] at he
  change (actualDifferentialCartier^[j + k + p])
      (actualBinaryRationalExtension ActualResidueField
        (actualBinaryRationalDifferential (actualLinkedCutoff (Phi v))
          (Polynomial.X ^ (actualLinkedOffset (Phi v) - 1) : Polynomial (ZMod 2)))) =
    (actualDifferentialCartier^[j + k])
      (actualBinaryRationalExtension ActualResidueField
        (actualBinaryRationalDifferential (actualLinkedCutoff (Phi v))
          (Polynomial.X ^ (actualLinkedOffset (Phi v) - 1) : Polynomial (ZMod 2)))) at he
  rw [actualBinaryRationalExtensionLinked] at he
  exact he

end LogicLineages.OrdinalComparison
