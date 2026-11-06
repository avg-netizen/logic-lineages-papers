module
public import LogicLineages.OrdinalComparison.CanonicalGuardSelector.Targets
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.ProgramsProof
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.CounterRangeWordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.MixedRangeWordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
open PolynomialGraphCompletion OuterShiftNormalization CounterWordGuardCompletion
open CounterRangeWordGuardCompletion MixedRangeWordGuardCompletion

theorem canonicalHead_primitive : Primrec canonicalHead := by
  have htag : Primrec (fun a : Letter => a.1) := Primrec.fst
  have hrest : Primrec (fun a : Letter => a.2) := Primrec.snd
  have hd := Primrec.fst.comp hrest
  have hcj := Primrec.snd.comp hrest
  have hc := Primrec.fst.comp hcj
  have hj := Primrec.snd.comp hcj
  have hquadratic : Primrec (fun a : Letter => quadraticLetter a.2.2.2) :=
    (Primrec.const 2).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair hj))
  have hkernel : Primrec (fun a : Letter => kernelLetter a.2.1 a.2.2.1 a.2.2.2) :=
    (Primrec.const 3).pair (hd.pair (hc.pair hj))
  have hcounter : Primrec (fun a : Letter => counterLetter a.2.1 a.2.2.1) :=
    (Primrec.const 4).pair (hd.pair (hc.pair (Primrec.const (0 : Int))))
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (Primrec.const phiLetter)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hquadratic
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) hkernel
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) hcounter Primrec.id)))

theorem viewPrefix_primitive : Primrec viewPrefix :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp
    (Primrec.list_reverse.comp OuterShiftNormalization.Proof.coreWord_primitive))

theorem rawHead_primitive : Primrec rawHead :=
  Primrec.option_getD.comp
    (Primrec.list_head?.comp
      (Primrec.list_reverse.comp OuterShiftNormalization.Proof.coreWord_primitive))
    (Primrec.const phiLetter)

theorem viewHead_primitive : Primrec viewHead :=
  canonicalHead_primitive.comp rawHead_primitive

theorem preparedWord_primitive : Primrec preparedWord := by
  have hs : Primrec shiftLetter :=
    (Primrec.const 0).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))
  have hsuffix : Primrec (fun w : Word => [shiftLetter (outerShift w)]) :=
    Primrec.list_cons.comp (hs.comp OuterShiftNormalization.Proof.outerShift_primitive)
      (Primrec.const [])
  exact Primrec.ite
    (Primrec.eq.comp OuterShiftNormalization.Proof.coreWord_primitive (Primrec.const []))
    hsuffix
    (Primrec.list_append.comp viewPrefix_primitive
      (Primrec.list_cons.comp viewHead_primitive hsuffix))

theorem selectHeads_primitive :
    Primrec (fun p : Word × Letter × Word × Letter =>
      selectHeads p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := Word × Letter × Word × Letter
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hB := Primrec.fst.comp hrest
  have hb := Primrec.snd.comp hrest
  have htagA := Primrec.fst.comp ha
  have htagB := Primrec.fst.comp hb
  have hdA := Primrec.fst.comp (Primrec.snd.comp ha)
  have hdB := Primrec.fst.comp (Primrec.snd.comp hb)
  have hcA := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hcB := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb))
  have hnA := Primrec.nat_sub.comp hdA (Primrec.const 3)
  have hnB := Primrec.nat_sub.comp hdB (Primrec.const 3)
  have hleaderA := Primrec.list_append.comp hA
    (CounterWordGuardCompletion.Proof.leaderWord_primitive.comp (hnA.pair hcA))
  have hleaderB := Primrec.list_append.comp hB
    (CounterWordGuardCompletion.Proof.leaderWord_primitive.comp (hnB.pair hcB))
  have hrangeA := CounterRangeWordGuardCompletion.Proof.rangeInputWord_primitive.comp
    (hA.pair ha)
  have hrangeB := CounterRangeWordGuardCompletion.Proof.rangeInputWord_primitive.comp
    (hB.pair hb)
  have hzeroA := MixedRangeWordGuardCompletion.Proof.retainedWord_primitive.comp
    (hA.pair ((Primrec.const 0).pair (hnA.pair hcA)))
  have hzeroB := MixedRangeWordGuardCompletion.Proof.retainedWord_primitive.comp
    (hB.pair ((Primrec.const 0).pair (hnB.pair hcB)))
  have hmixedA := MixedRangeWordGuardCompletion.Proof.retainedWord_primitive.comp
    (hA.pair ((Primrec.nat_add.comp hnB (Primrec.const 1)).pair
      ((Primrec.nat_sub.comp (Primrec.nat_sub.comp hdA hdB) (Primrec.const 1)).pair hcA)))
  have hmixedB := MixedRangeWordGuardCompletion.Proof.retainedWord_primitive.comp
    (hB.pair ((Primrec.nat_add.comp hnA (Primrec.const 1)).pair
      ((Primrec.nat_sub.comp (Primrec.nat_sub.comp hdB hdA) (Primrec.const 1)).pair hcB)))
  exact Primrec.ite (Primrec.eq.comp htagA (Primrec.const 4))
    (Primrec.ite (Primrec.eq.comp htagB (Primrec.const 4))
      ((Primrec.const 1).pair ((Primrec.const false).pair (hleaderA.pair hleaderB)))
      ((Primrec.const 2).pair ((Primrec.const false).pair (hleaderA.pair hrangeB))))
    (Primrec.ite (Primrec.eq.comp htagB (Primrec.const 4))
      ((Primrec.const 2).pair ((Primrec.const true).pair (hrangeA.pair hleaderB)))
      (Primrec.ite (Primrec.eq.comp htagA (Primrec.const 1))
        ((Primrec.const 3).pair ((Primrec.const false).pair (hA.pair hrangeB)))
        (Primrec.ite (Primrec.eq.comp htagB (Primrec.const 1))
          ((Primrec.const 3).pair ((Primrec.const true).pair (hrangeA.pair hB)))
          (Primrec.ite (Primrec.eq.comp htagA (Primrec.const 2))
            (Primrec.ite (Primrec.eq.comp htagB (Primrec.const 2))
              ((Primrec.const 4).pair ((Primrec.const false).pair (hA.pair hB)))
              ((Primrec.const 7).pair ((Primrec.const true).pair (hA.pair hzeroB))))
            (Primrec.ite (Primrec.eq.comp htagB (Primrec.const 2))
              ((Primrec.const 7).pair ((Primrec.const false).pair (hzeroA.pair hB)))
              (Primrec.ite (Primrec.eq.comp hdA hdB)
                ((Primrec.const 5).pair ((Primrec.const false).pair (hA.pair hB)))
                (Primrec.ite (Primrec.nat_lt.comp hdB hdA)
                  ((Primrec.const 6).pair ((Primrec.const false).pair (hmixedA.pair hB)))
                  ((Primrec.const 6).pair
                    ((Primrec.const true).pair (hA.pair hmixedB))))))))))

theorem selectWords_primitive :
    Primrec (fun p : Word × Word => selectWords p.1 p.2) := by
  have htest : PrimrecPred (fun p : Word × Word =>
      coreWord p.1 = [] ∨ coreWord p.2 = []) :=
    (Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.fst)
      (Primrec.const [])).or
      (Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.snd)
        (Primrec.const []))
  exact Primrec.ite htest (Primrec.const none)
    (Primrec.option_some.comp (selectHeads_primitive.comp
      ((viewPrefix_primitive.comp Primrec.fst).pair
        ((viewHead_primitive.comp Primrec.fst).pair
          ((viewPrefix_primitive.comp Primrec.snd).pair
            (viewHead_primitive.comp Primrec.snd))))))

theorem selectorPrograms : Targets.SelectorPrograms :=
  ⟨canonicalHead_primitive, viewPrefix_primitive, rawHead_primitive, viewHead_primitive,
    preparedWord_primitive, selectHeads_primitive, selectWords_primitive⟩

end LogicLineages.OrdinalComparison.CanonicalGuardSelector.Proof
