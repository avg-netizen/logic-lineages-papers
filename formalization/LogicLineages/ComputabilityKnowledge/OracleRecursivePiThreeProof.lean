module

public import LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeTargets
public import LogicLineages.ComputabilityKnowledge.OraclePiThreeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeProof
open OraclePiThree OracleRecursivePiThree OracleRecursivePiThreeTargets PredictionLearning

private abbrev Data := Nat.Partrec.Code × Nat × Nat × Nat × Nat

private theorem pr_observation : Primrec (fun a : Data => observationMatrix a.1 a.2) := by
  have hi : Primrec (fun a : Data => a.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun a : Data => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec (fun a : Data => a.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hw : Primrec (fun a : Data => a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hz := Primrec.fst.comp (Primrec.unpair.comp hw)
  have ht := Primrec.snd.comp (Primrec.unpair.comp hw)
  have heval := Nat.Partrec.Code.primrec_evaln.comp
    ((ht.pair Primrec.fst).pair (Primrec.encode.comp (hi.pair (hx.pair (hy.pair hz)))))
  apply (Primrec.not.comp ((Primrec.eq.comp heval (Primrec.const (some 0))).decide)).of_eq
  intro a
  simp [observationMatrix]

theorem uniformObservationPrimrec : UniformObservationPrimrec := by
  refine ⟨pr_observation, ?_⟩
  have hp : Primrec (fun a : Nat × Nat × Nat × Nat => a.1.unpair) :=
    Primrec.unpair.comp Primrec.fst
  have hc := (Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp hp)
  have hi := Primrec.snd.comp hp
  have hx : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hw : Primrec (fun a : Nat × Nat × Nat × Nat => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hmap := hc.pair (hi.pair (hx.pair (hy.pair hw)))
  apply (pr_observation.comp hmap).of_eq
  intro a
  dsimp only [codedObservation]

private theorem comp_bitValue : Computable bitValue :=
  ((Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq
    (fun b => by cases b <;> rfl)).to_comp

theorem recursiveMatrixCompiler : RecursiveMatrixCompiler := by
  intro R hR
  have hf : Computable (fun n : Nat => bitValue (R (Denumerable.ofNat (Nat × Nat × Nat × Nat) n))) :=
    comp_bitValue.comp (hR.comp (Primrec.ofNat (Nat × Nat × Nat × Nat)).to_comp)
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  refine ⟨code, fun a => ?_⟩
  rw [hc]
  change Part.some (bitValue (R (Denumerable.ofNat _ (Encodable.encode a)))) = _
  rw [Denumerable.ofNat_encode]

theorem universalObservationCalibration : UniversalObservationCalibration := by
  intro R code hc i x y
  constructor
  · intro hobs z
    cases hz : R (i, x, y, z) with
    | true => rfl
    | false =>
      have hzero : 0 ∈ code.eval (Encodable.encode (i, x, y, z)) := by
        rw [hc]
        simp [hz, bitValue]
      obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hzero
      have hfuel' := Option.mem_def.mp hfuel
      have hn := hobs (Nat.pair z fuel)
      simp only [observationMatrix, Nat.unpair_pair] at hn
      rw [hfuel'] at hn
      simp at hn
  · intro htrue w
    change decide (_ ≠ some 0) = true
    apply decide_eq_true_iff.mpr
    intro hz
    have hzero := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hz)
    rw [hc, htrue] at hzero
    simp [bitValue] at hzero

theorem uniformCodedThirdJumpDecision : UniformCodedThirdJumpDecision :=
  OraclePiThreeProof.actualPiThreeThirdJumpDecision codedObservation uniformObservationPrimrec.2

theorem actualRecursiveThirdJumpDecision : ActualRecursiveThirdJumpDecision := by
  classical
  intro R hR
  obtain ⟨code, hc⟩ := recursiveMatrixCompiler R hR
  have hcal : ∀ i : Nat, matrixIndicator codedObservation (Nat.pair (Encodable.encode code) i) =
      matrixIndicator R i := by
    intro i
    have hprop : (∀ x, ∃ y, ∀ w, codedObservation (Nat.pair (Encodable.encode code) i, x, y, w) = true) ↔
        ∀ x, ∃ y, ∀ z, R (i, x, y, z) = true := by
      apply forall_congr'
      intro x
      apply exists_congr
      intro y
      simpa only [codedObservation, Nat.unpair_pair, Denumerable.ofNat_encode] using
        universalObservationCalibration R code hc i x y
    unfold matrixIndicator
    rw [propext hprop]
  have hquery : Primrec (fun i => Nat.pair (Encodable.encode code) i) :=
    Primrec₂.natPair.comp (Primrec.const _) Primrec.id
  have h := OracleRelativeRecursionProof.relativeComposition _ _ _
    uniformCodedThirdJumpDecision hquery.computableIn
  apply h.of_eq
  intro i
  change Part.some (matrixIndicator codedObservation (Nat.pair (Encodable.encode code) i)) = _
  rw [hcal]

end LogicLineages.ComputabilityKnowledge.OracleRecursivePiThreeProof
