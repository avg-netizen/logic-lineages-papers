module

public import LogicLineages.ComputabilityKnowledge.OracleJumpTargets
public import LogicLineages.ComputabilityKnowledge.OracleUniversalProof
public import LogicLineages.ComputabilityKnowledge.OracleRelativeRecursionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleJumpProof
open OracleProgram OracleUniversal OracleJump OracleJumpTargets

theorem actualJumpCharacteristic : ActualJumpCharacteristic := by
  classical
  intro g query
  simp [jump]

theorem zeroOracleUniversalPartrec : ZeroOracleUniversalPartrec := by
  have h : RecursiveIn {fun _ => Part.some 0} (universal zeroOracle) := by
    simpa only [zeroOracle] using OracleUniversalProof.relativeUniversalEvaluation zeroOracle
  exact h.partrec_of_const

theorem ordinaryToFirstCalibration : OrdinaryToFirstCalibration := by
  classical
  have hp : Primrec ordinaryToFirst :=
    Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0) (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair)
  refine ⟨hp, ?_⟩
  intro query
  have he : universal zeroOracle (ordinaryToFirst query) =
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code query.unpair.1) query.unpair.2 := by
    apply Part.ext
    intro output
    have h := OracleUniversalProof.encodedUniversalSemantics zeroOracle
      (.base (Denumerable.ofNat Nat.Partrec.Code query.unpair.1)) query.unpair.2 output
    simpa only [encode, Denumerable.encode_ofNat, eval, ordinaryToFirst] using h
  simp only [firstJump, jump, ordinaryIndicator, ordinaryHalting, he]
  split_ifs <;> rfl

theorem firstToOrdinaryCalibration : FirstToOrdinaryCalibration := by
  classical
  obtain ⟨compiler, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp zeroOracleUniversalPartrec)
  refine ⟨compiler, fun query => congrFun hc query,
    Primrec₂.natPair.comp (Primrec.const _) Primrec.id, ?_⟩
  intro query
  simp only [ordinaryIndicator, ordinaryHalting, firstToOrdinary, Nat.unpair_pair,
    Denumerable.ofNat_encode, firstJump, jump]
  rw [congrFun hc query]

theorem firstJumpRelativeEquivalence : FirstJumpRelativeEquivalence := by
  obtain ⟨compiler, _, hp, hc⟩ := firstToOrdinaryCalibration
  constructor
  · have ho : ComputableIn {fun n => Part.some (ordinaryIndicator n)} ordinaryIndicator :=
      RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ rfl)
    have h := OracleRelativeRecursionProof.relativeComposition _ _ _ ho hp.computableIn
    apply h.of_eq
    intro query
    exact congrArg Part.some (hc query)
  · have ho : ComputableIn {fun n => Part.some (firstJump n)} firstJump :=
      RecursiveIn.iff_nat.mpr (Nat.RecursiveIn.oracle _ rfl)
    have h := OracleRelativeRecursionProof.relativeComposition _ _ _ ho ordinaryToFirstCalibration.1.computableIn
    apply h.of_eq
    intro query
    exact congrArg Part.some (ordinaryToFirstCalibration.2 query)

end LogicLineages.ComputabilityKnowledge.OracleJumpProof
