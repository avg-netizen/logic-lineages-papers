module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchTargets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProgramsProof
private import LogicLineages.OrdinalComparison.CanonicalGuardSelector.ProgramsProof
private import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.QuadraticWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.ShiftedEqualRankWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.OuterShiftNormalization.ProgramsProof
private import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof
private import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProgramsProof
open PolynomialGraphCompletion CanonicalGuardSelector OuterShiftNormalization
open ComparisonProgramsProof

theorem forwardTail_primitive :
    Primrec (fun p : Nat × Word × Letter × Word × Letter × Int × Int =>
      forwardTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
        p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  let P := Nat × Word × Letter × Word × Letter × Int × Int
  have hcode : Primrec (fun p : P => p.1) := Primrec.fst
  have hA : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hB := Primrec.fst.comp hr3
  have hr4 := Primrec.snd.comp hr3
  have hb := Primrec.fst.comp hr4
  have hjk := Primrec.snd.comp hr4
  have hj := Primrec.fst.comp hjk
  have hk := Primrec.snd.comp hjk
  have hdA := Primrec.fst.comp (Primrec.snd.comp ha)
  have hdB := Primrec.fst.comp (Primrec.snd.comp hb)
  have hcA := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hcB := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hiA := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hiB := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hnA := Primrec.nat_sub.comp hdA (Primrec.const 3)
  have hnB := Primrec.nat_sub.comp hdB (Primrec.const 3)
  have hgap := Primrec.nat_sub.comp (Primrec.nat_sub.comp hdA hdB) (Primrec.const 1)
  have h1 := CounterWordGuardCompletion.Proof.guardTail_primitive.comp
    (hA.pair (hB.pair (hnA.pair (hnB.pair (hcA.pair (hcB.pair (hj.pair hk)))))))
  have h2 := CounterRangeWordGuardCompletion.Proof.guardTail_primitive.comp
    (hA.pair (hB.pair (hnA.pair (hcA.pair (hb.pair (hj.pair hk))))))
  have h3 := ShiftedPhiRangeWordGuardCompletion.Proof.guardTail_primitive.comp
    (hA.pair (hB.pair (hb.pair (hj.pair hk))))
  have h4 := QuadraticWordGuardCompletion.Proof.guardTail_primitive.comp
    (hA.pair (hB.pair (hiA.pair (hiB.pair (hj.pair hk)))))
  have h5 := ShiftedEqualRankWordGuardCompletion.Proof.guardTail_primitive.comp
    (hA.pair (hB.pair (hdA.pair (hcA.pair (hcB.pair
      (hiA.pair (hiB.pair (hj.pair hk))))))))
  have h6 := MixedRangeWordGuardCompletion.Proof.kernelGuardTail_primitive.comp
    (hA.pair (hB.pair (hnB.pair (hgap.pair (hcA.pair (hcB.pair
      (hiA.pair (hiB.pair (hj.pair hk)))))))))
  have h7 := MixedRangeWordGuardCompletion.Proof.quadraticGuardTail_primitive.comp
    (hA.pair (hB.pair (hnA.pair (hcA.pair (hiA.pair (hiB.pair (hj.pair hk)))))))
  exact Primrec.ite (Primrec.eq.comp hcode (Primrec.const 1)) h1
    (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 2)) h2
      (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 3)) h3
        (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 4)) h4
          (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 5)) h5
            (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 6)) h6
              (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 7)) h7
                (Primrec.const 0)))))))

theorem forwardTie_primitive :
    Primrec (fun p : Nat × Letter × Letter × Int × Int =>
      forwardTie p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let P := Nat × Letter × Letter × Int × Int
  have hcode : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hb := Primrec.fst.comp hr2
  have hjk := Primrec.snd.comp hr2
  have hj := Primrec.fst.comp hjk
  have hk := Primrec.snd.comp hjk
  have hdA := Primrec.fst.comp (Primrec.snd.comp ha)
  have hdB := Primrec.fst.comp (Primrec.snd.comp hb)
  have hcA := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hcB := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hiA := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hiB := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hnA := Primrec.nat_sub.comp hdA (Primrec.const 3)
  have hnB := Primrec.nat_sub.comp hdB (Primrec.const 3)
  have houter := orderInt_primitive.comp hj hk
  have hinner := orderInt_primitive.comp hiA hiB
  have h1 := lexOrder_primitive.comp (orderNat_primitive.comp hnA hnB) houter
  have h4 := lexOrder_primitive.comp hinner houter
  have h56 := lexOrder_primitive.comp (orderNat_primitive.comp hcB hcA) h4
  have hceil := Primrec.nat_div.comp
    (Primrec.nat_add.comp hcA (Primrec.const 1)) (Primrec.const 2)
  have hshift : Primrec (fun p : P =>
      p.2.1.2.2.2 - (((p.2.1.2.2.1+1)/2 : Nat) : Int)) := by
    apply (LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp hiA
      (LayeredComparison.IntegerAlgorithms.Proof.negate_primitive.comp
        (LayeredComparison.IntegerAlgorithms.Proof.ofNat_primitive.comp hceil))).of_eq
    intro p
    simp only [sub_eq_add_neg]
  have h7 := lexOrder_primitive.comp (orderInt_primitive.comp hshift hiB) houter
  exact Primrec.ite (Primrec.eq.comp hcode (Primrec.const 1)) h1
    (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 2)) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 3)) houter
        (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 4)) h4
          (Primrec.ite
            ((Primrec.eq.comp hcode (Primrec.const 5)).or
              (Primrec.eq.comp hcode (Primrec.const 6))) h56
            (Primrec.ite (Primrec.eq.comp hcode (Primrec.const 7)) h7
              (Primrec.const 1))))))

theorem headTail_primitive :
    Primrec (fun p : Word × Letter × Word × Letter × Int × Int =>
      headTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let P := Word × Letter × Word × Letter × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr2 : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hB := Primrec.fst.comp hr2
  have hr3 := Primrec.snd.comp hr2
  have hb := Primrec.fst.comp hr3
  have hjk := Primrec.snd.comp hr3
  have hj := Primrec.fst.comp hjk
  have hk := Primrec.snd.comp hjk
  have hq := CanonicalGuardSelector.Proof.selectHeads_primitive.comp
    (hA.pair (ha.pair (hB.pair hb)))
  have hcode := Primrec.fst.comp hq
  have hrev := Primrec.fst.comp (Primrec.snd.comp hq)
  exact Primrec.ite (Primrec.eq.comp hrev (Primrec.const true))
    (forwardTail_primitive.comp (hcode.pair (hB.pair (hb.pair
      (hA.pair (ha.pair (hk.pair hj)))))))
    (forwardTail_primitive.comp (hcode.pair (hA.pair (ha.pair
      (hB.pair (hb.pair (hj.pair hk)))))))

theorem headTie_primitive :
    Primrec (fun p : Letter × Letter × Int × Int =>
      headTie p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Letter × Letter × Int × Int
  have ha : Primrec (fun p : P => p.1) := Primrec.fst
  have hb : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hjk : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hj := Primrec.fst.comp hjk
  have hk := Primrec.snd.comp hjk
  have hq := CanonicalGuardSelector.Proof.selectHeads_primitive.comp
    ((Primrec.const ([] : Word)).pair (ha.pair ((Primrec.const ([] : Word)).pair hb)))
  have hcode := Primrec.fst.comp hq
  have hrev := Primrec.fst.comp (Primrec.snd.comp hq)
  exact Primrec.ite (Primrec.eq.comp hrev (Primrec.const true))
    (reverseOrder_primitive.comp
      (forwardTie_primitive.comp (hcode.pair (hb.pair (ha.pair (hk.pair hj))))))
    (forwardTie_primitive.comp (hcode.pair (ha.pair (hb.pair (hj.pair hk)))))

theorem dispatchTail_primitive : Primrec (fun p : Word × Word => dispatchTail p.1 p.2) :=
  Primrec.nat_max.comp (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.fst)
    (Primrec.nat_max.comp (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.snd)
      (headTail_primitive.comp
        ((CanonicalGuardSelector.Proof.viewPrefix_primitive.comp Primrec.fst).pair
          ((CanonicalGuardSelector.Proof.viewHead_primitive.comp Primrec.fst).pair
            ((CanonicalGuardSelector.Proof.viewPrefix_primitive.comp Primrec.snd).pair
              ((CanonicalGuardSelector.Proof.viewHead_primitive.comp Primrec.snd).pair
                ((OuterShiftNormalization.Proof.outerShift_primitive.comp Primrec.fst).pair
                  (OuterShiftNormalization.Proof.outerShift_primitive.comp Primrec.snd))))))))

theorem dispatchTie_primitive : Primrec (fun p : Word × Word => dispatchTie p.1 p.2) :=
  headTie_primitive.comp
    ((CanonicalGuardSelector.Proof.viewHead_primitive.comp Primrec.fst).pair
      ((CanonicalGuardSelector.Proof.viewHead_primitive.comp Primrec.snd).pair
        ((OuterShiftNormalization.Proof.outerShift_primitive.comp Primrec.fst).pair
          (OuterShiftNormalization.Proof.outerShift_primitive.comp Primrec.snd))))

theorem dispatchPrograms : DispatchTargets.DispatchPrograms :=
  ⟨dispatchTail_primitive, dispatchTie_primitive⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.DispatchProgramsProof
