module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadCodeCalibrationProof
import LogicLineages.OrdinalComparison.PeakWordProgramWordProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
open LayeredComparison.IntegerAlgorithms.Proof

theorem shiftLetter_primitive : Primrec shiftLetter :=
  (Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))

theorem quadraticLetter_primitive : Primrec quadraticLetter :=
  (Primrec.const 2).pair ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))

theorem kernelLetter_primitive :
    Primrec (fun p : Nat × Nat × Int => kernelLetter p.1 p.2.1 p.2.2) :=
  (Primrec.const 3).pair (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))

theorem counterLetter_primitive : Primrec₂ counterLetter :=
  (Primrec.const 4).pair (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (0 : Int))))

private theorem halfMass_primitive :
    Primrec (fun p : Call => (((p.2+1)/2 : Nat) : Int)) :=
  ofNat_primitive.comp (Primrec.nat_div.comp
    (Primrec.succ.comp Primrec.snd) (Primrec.const 2))

theorem rangeLetter_primitive : Primrec rangeLetter := by
  have hquadratic : Primrec (fun p : Call =>
      quadraticLetter (-(((p.2+1)/2 : Nat) : Int))) :=
    quadraticLetter_primitive.comp (negate_primitive.comp halfMass_primitive)
  have hkernel : Primrec (fun p : Call => kernelLetter p.1 p.2 0) :=
    kernelLetter_primitive.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (0 : Int))))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
    (Primrec.const phiLetter)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) hquadratic hkernel)

theorem countContribution_primitive : Primrec countContribution := by
  have hconstant : Primrec (fun p : Call => 2-2*(((p.2+1)/2 : Nat) : Int)) := by
    apply (add_primitive.comp (Primrec.const (2 : Int))
      (negate_primitive.comp (mul_primitive.comp (Primrec.const (2 : Int))
        halfMass_primitive))).of_eq
    intro p
    simp only [sub_eq_add_neg]
  have hquadratic : Primrec (fun p : Call =>
      ((2-2*(((p.2+1)/2 : Nat) : Int)),[(1,[phiLetter])] : UnaryRow)) :=
    hconstant.pair (Primrec.const [(1,[phiLetter])])
  have hcounter : Primrec (fun p : Call => ((0,[(2,[counterLetter p.1 p.2])]) : UnaryRow)) :=
    (Primrec.const (0 : Int)).pair
      (Primrec.list_cons.comp ((Primrec.const (2 : Int)).pair
        (Primrec.list_cons.comp counterLetter_primitive (Primrec.const [])))
        (Primrec.const []))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
    (Primrec.const (2,[]))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2)) hquadratic hcounter)

theorem addUnary_primitive : Primrec₂ addUnary :=
  (add_primitive.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem prepend_primitive : Primrec₂ prepend := by
  have hw : Primrec (fun p : (Word × UnaryRow) × (Int × Word) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hc : Primrec (fun p : (Word × UnaryRow) × (Int × Word) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (Word × UnaryRow) × (Int × Word) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hm : Primrec (fun p : Word × UnaryRow =>
      p.2.2.map (fun a => (a.1,p.1++a.2))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (hc.pair (Primrec.list_append.comp hw ht)).to₂
  exact (Primrec.fst.comp Primrec.snd).pair hm

theorem compileCalls_primitive : Primrec compileCalls := by
  have hs : Primrec (fun p : Call × UnaryRow =>
      addUnary (countContribution p.1) (prepend [rangeLetter p.1] p.2)) :=
    addUnary_primitive.comp (countContribution_primitive.comp Primrec.fst)
      (prepend_primitive.comp
        (Primrec.list_cons.comp (rangeLetter_primitive.comp Primrec.fst) (Primrec.const []))
        Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const (0,[(2,[])]))
    (hs.comp Primrec.snd).to₂

theorem headCalls_primitive : Primrec headCalls := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hs : Primrec (fun p : Nat × (Nat × Nat) => (rawNormCode p.2.1,p.2.2)) :=
    (hn.comp (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_map PeakWordProgram.peak.1 hs.to₂

theorem headRow_primitive : Primrec headRow := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hs : Primrec (fun code : Nat => [shiftLetter (rawNormCode code : Int)]) :=
    Primrec.list_cons.comp (shiftLetter_primitive.comp (ofNat_primitive.comp hn))
      (Primrec.const [])
  exact prepend_primitive.comp hs (compileCalls_primitive.comp headCalls_primitive)

theorem headDegree_primitive : Primrec headDegree :=
  Primrec.nat_add.comp (Primrec.const 3) (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive)

private theorem naturalSum_primitive : Primrec (fun xs : List Nat => xs.sum) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem familyDegree_primitive : Primrec familyDegree := by
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have hm : Primrec (fun codes : List Nat => codes.map rawNormCode) :=
    Primrec.list_map Primrec.id (hn.comp Primrec.snd).to₂
  exact Primrec.nat_add.comp (Primrec.const 3) (naturalSum_primitive.comp hm)

theorem headEquation_primitive :
    Primrec (fun p : Nat × Nat × Nat => headEquation p.1 p.2.1 p.2.2) := by
  let Input := Nat × Nat × Nat
  have hr : Primrec (fun p : Input => headRow p.1) :=
    headRow_primitive.comp Primrec.fst
  have hz : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun p : Input × (Int × Word) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hc : Primrec (fun p : Input × (Int × Word) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hw : Primrec (fun p : Input × (Int × Word) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hm : Primrec (fun p : Input =>
      (headRow p.1).2.map (fun a => (-a.1,p.2.1,a.2))) :=
    Primrec.list_map (Primrec.snd.comp hr)
      ((negate_primitive.comp hc).pair (hi.pair hw)).to₂
  have hout : Primrec (fun p : Input => ((2 : Int),p.2.2,([] : Word))) :=
    (Primrec.const (2 : Int)).pair (hz.pair (Primrec.const []))
  exact (negate_primitive.comp (Primrec.fst.comp hr)).pair
    (Primrec.list_cons.comp hout hm)

theorem headPrograms : Targets.HeadPrograms :=
  ⟨headCalls_primitive,compileCalls_primitive,headRow_primitive,
    headDegree_primitive,familyDegree_primitive,headEquation_primitive⟩

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
