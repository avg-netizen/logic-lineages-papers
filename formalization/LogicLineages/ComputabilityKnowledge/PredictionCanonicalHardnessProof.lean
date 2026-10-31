module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsProof
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalClassificationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessProof
open PredictionCanonicalHardness PredictionCanonicalHardnessTargets PredictionCanonicalTapeBounds
open PredictionTapeObservation PredictionOriginalMeasureAlgorithm

private theorem indicator_iff (R : OraclePiThree.Matrix) (p : Nat) :
    OraclePiThree.matrixIndicator R p=1 ↔ ∀ x,∃ y,∀ z,R (p,x,y,z)=true := by
  classical
  simp only [OraclePiThree.matrixIndicator]
  split_ifs <;> simp_all

private theorem value_mem (c : Nat.Partrec.Code) (hc : PredictionCanonicalList.TotalNat c) (n : Nat) :
    PredictionMaximum.evalValue c n ∈ Nat.Partrec.Code.eval c n := by
  have hd : (Nat.Partrec.Code.eval c n).Dom := (hc n).choose_spec.1
  simp only [PredictionMaximum.evalValue, dif_pos hd]
  exact ⟨hd,rfl⟩

theorem canonicalFixedThresholds : CanonicalFixedThresholds := by
  classical
  obtain ⟨i,hi⟩ := PredictionCanonicalTapeBoundsProof.exactCanonicalCoverage.1 Nat.succ Computable.succ
  obtain ⟨u,_,hu⟩ := PredictionThirdJumpThresholdProof.uniformThirdJumpThreshold
  obtain ⟨v,_,hv⟩ := PredictionCanonicalTapeBoundsProof.actualSecondJumpBoundIndices
  refine ⟨i+1,by omega,?_⟩
  intro m hm
  have hpos : 1 ≤ m := by omega
  have hs := hv (m-1)
  let bound := Denumerable.ofNat Nat.Partrec.Code (positiveIndex v (m-1))
  have hvalues : ∀ n,PredictionMaximum.evalValue bound n = PredictionOriginalBounds.levelBound listing m n := by
    intro n
    simpa only [Nat.sub_add_cancel hpos] using hs.2 n
  have hb : Computable (PredictionOriginalBounds.levelBound listing m) := by
    have hpart : Partrec (fun n => Nat.Partrec.Code.eval bound n) :=
      Nat.Partrec.Code.eval_part.comp (Computable.const bound) Computable.id
    apply hpart.of_eq_tot
    intro n
    rw [← hvalues n]
    exact value_mem bound hs.1 n
  have horder : ∀ p (hp : TotalBinary p), ThresholdPredicate m p hp ↔
      PredictionTapeRuntimeClass.Threshold (policy p hp) (PredictionOriginalBounds.levelBound listing m) := by
    intro p hp
    exact PredictionMeasureOrderProof.positiveThresholdOrder _
      (PredictionOriginalBounds.monotoneLevels listing) _ m hpos
  have hsucc : ∀ n,n+1 ≤ PredictionOriginalBounds.levelBound listing m n := by
    intro n
    have hin : listing i n = n+1 := hi n
    rw [PredictionOriginalBounds.literalFiniteMaximum]
    calc
      n+1 = listing i n := hin.symm
      _ ≤ _ := le_trans
        (Finset.le_sup (b := n) (s := Finset.range (n+1)) (f := listing i) (by simp))
        (Finset.le_sup (b := i) (s := Finset.range m)
          (f := fun j => (Finset.range (n+1)).sup (listing j)) (by simp only [Finset.mem_range]; omega))
  constructor
  · let M : OraclePiThree.Matrix := fun z => PredictionThirdJumpThreshold.packedMatrix u
      (Nat.pair z.1 (Encodable.encode bound),z.2.1,z.2.2.1,z.2.2.2)
    refine ⟨M,?_,?_⟩
    · exact (PredictionThirdJumpThresholdProof.effectivePackedMatrix u).comp
        ((Primrec₂.natPair.comp Primrec.fst (Primrec.const (Encodable.encode bound))).pair Primrec.snd)
    · intro p hp
      have ht := hu p hp bound hs.1
      rw [show PredictionMaximum.evalValue bound = PredictionOriginalBounds.levelBound listing m from funext hvalues] at ht
      exact (horder p hp).trans (ht.symm.trans (indicator_iff _ _))
  · intro R hR
    have hevad : ∀ k, ∃ N,∀ n,N ≤ n → min k n+2 < PredictionOriginalBounds.levelBound listing m n := by
      intro k
      refine ⟨k+2,?_⟩
      intro n hn
      have hmin := Nat.min_le_left k n
      have hh := hsucc n
      omega
    obtain ⟨f,hf,hp,hsem⟩ := PredictionTapeHardnessProof.fixedBudgetHardness R _ hR hb hevad
    exact ⟨f,hf,hp,fun z => (horder (f z) (hp z)).trans (hsem z)⟩

theorem actualCanonicalMeasureLower : ActualCanonicalMeasureLower := by
  classical
  intro A hA
  obtain ⟨R,hR,hjump⟩ := OracleThirdJumpNormalFormProof.recursiveActualThirdJumpComplement
  obtain ⟨m,hm,hcomplete⟩ := canonicalFixedThresholds
  obtain ⟨f,hf,hp,hs⟩ := (hcomplete m le_rfl).2 R hR
  have hread : Primrec (fun a => PredictionOriginalComparator.compareOutputs a (m+1)) :=
    PredictionOriginalComparatorProof.exactOutputComparison.1.comp Primrec.id (Primrec.const (m+1))
  have ho : ComputableIn {fun n => Part.some (A n)} A := RecursiveIn.oracle _ rfl
  have hquery := OracleRelativeRecursionProof.relativeComposition _ _ _ ho hf.computableIn
  apply (OracleRelativeRecursionProof.relativeComposition _ _ _ hread.computableIn hquery).of_eq
  intro z
  change Part.some (PredictionOriginalComparator.compareOutputs (A (f z)) (m+1)) = Part.some (OraclePiThree.thirdJump z)
  congr 1
  have hc := PredictionOriginalComparatorProof.exactOutputComparison.2 (A (f z)) (m+1)
  have hiff : PredictionOriginalComparator.compareOutputs (A (f z)) (m+1)=1 ↔ OraclePiThree.thirdJump z ≠ 0 := by
    rw [hc.2, hA (f z) (hp z)]
    have hout : outputValue (m+1) = (m : WithTop Nat) := by simp [outputValue]
    rw [hout, lt_iff_not_ge]
    exact (not_congr (hs z)).trans (not_congr (hjump z))
  have hj : OraclePiThree.thirdJump z=0 ∨ OraclePiThree.thirdJump z=1 := by
    simp only [OraclePiThree.thirdJump, OracleJump.jump]
    split_ifs <;> simp
  rcases hj with hz|hz
  · have hn : PredictionOriginalComparator.compareOutputs (A (f z)) (m+1) ≠ 1 := by
      intro h
      exact (hiff.mp h) hz
    rcases hc.1 with h0|h1
    · exact h0.trans hz.symm
    · contradiction
  · have hn : OraclePiThree.thirdJump z ≠ 0 := by omega
    exact (hiff.mpr hn).trans hz.symm

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalHardnessProof
