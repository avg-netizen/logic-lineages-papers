module
public import LogicLineages.ControlSensitivityCurrent.RawBooleanMatrixTargets
public import LogicLineages.ControlSensitivityCurrent.RawBinaryPlanStepPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix

open PrimitiveGate (GateCode)
open BinaryPlanCompiler (shiftPort shift_port_primitive)

theorem bit_code_primitive : Primrec bitCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 9) Primrec.id) (Primrec.const 1)

theorem auxiliary_code_primitive : Primrec₂ auxiliaryCode :=
  (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 9) Primrec.fst) Primrec.snd) (Primrec.const 2)).to₂

theorem one_code_primitive : Primrec oneCode := bit_code_primitive

theorem local_raw_primitive :
    Primrec (fun p : Nat × List Nat × Nat × RowCode => localRaw p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × List Nat × Nat × RowCode
  have hm : Primrec (fun p : A => p.1) := Primrec.fst
  have hports : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrow : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htag := Primrec.fst.comp hrow
  have ha := Primrec.fst.comp (Primrec.snd.comp hrow)
  have hb := Primrec.snd.comp (Primrec.snd.comp hrow)
  have one := one_code_primitive.comp hm
  have input (idx : A → Nat) (hidx : Primrec idx) :
      Primrec (fun (p : A) => shiftPort (oneCode p.1) (p.2.1.getD (idx p) 0)) :=
    shift_port_primitive.comp (one.pair ((Primrec.list_getD 0).comp hports hidx))
  have x := input _ ha
  have y := input _ hb
  have prior (idx : A → Nat) (hidx : Primrec idx) : Primrec (fun (p : A) => bitCode (p.2.2.1 + idx p + 1)) :=
    bit_code_primitive.comp (Primrec.nat_add.comp (Primrec.nat_add.comp hi hidx) (Primrec.const 1))
  have priorA := prior _ ha
  have priorB := prior _ hb
  have out := bit_code_primitive.comp hi
  have z (j : Nat) : Primrec (fun p : A => auxiliaryCode p.2.2.1 j) :=
    auxiliary_code_primitive.comp hi (Primrec.const j)
  have zero : Primrec (fun _ : A => (0 : Nat)) := Primrec.const 0
  have eq {a b : A → Nat} (ha : Primrec a) (hb : Primrec b) : Primrec (fun p => eqCode (a p) (b p)) :=
    (Primrec.const 0).pair (ha.pair (hb.pair (Primrec.const (0,0))))
  have add {a b c : A → Nat} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
      Primrec (fun p => addCode (a p) (b p) (c p)) :=
    (Primrec.const 1).pair (ha.pair (hb.pair (hc.pair (Primrec.const 0))))
  have sort {a b l h : A → Nat} (ha : Primrec a) (hb : Primrec b) (hl : Primrec l) (hh : Primrec h) :
      Primrec (fun p => sortCode (a p) (b p) (l p) (h p)) :=
    (Primrec.const 2).pair (ha.pair (hb.pair (hl.pair hh)))
  have nil : Primrec (fun _ : A => ([] : List GateCode)) := Primrec.const []
  have cons {g : A → GateCode} {gs : A → List GateCode} (hg : Primrec g) (hgs : Primrec gs) :
      Primrec (fun p => g p :: gs p) := Primrec.list_cons.comp hg hgs
  have hz567 := cons (eq (z 5) zero) (cons (eq (z 6) zero) (cons (eq (z 7) zero) nil))
  have heq := cons (sort x y (z 0) (z 1))
    (cons (add (z 0) (z 2) (z 1)) (cons (sort (z 2) one (z 3) (z 4))
      (cons (add out (z 3) one) hz567)))
  have hle := cons (sort x y (z 0) (z 1)) (cons (sort (z 1) y (z 2) (z 3))
    (cons (add (z 2) (z 4) (z 3)) (cons (sort (z 4) one (z 5) (z 6))
      (cons (add out (z 5) one) (cons (eq (z 7) zero) nil)))))
  have hlt := cons (sort y x (z 0) (z 1)) (cons (sort (z 1) x (z 2) (z 3))
    (cons (add (z 2) (z 4) (z 3)) (cons (sort (z 4) one (z 5) (z 6))
      (cons (add (z 7) (z 5) one) (cons (add out (z 7) one) nil)))))
  have hz234 := cons (eq (z 2) zero) (cons (eq (z 3) zero) (cons (eq (z 4) zero) hz567))
  have hneg := cons (add out priorA one) (cons (eq (z 0) zero) (cons (eq (z 1) zero) hz234))
  have hconj := cons (sort priorA priorB (z 0) (z 1)) (cons (eq out (z 0)) hz234)
  have hdisj := cons (sort priorA priorB (z 0) (z 1)) (cons (eq out (z 1)) hz234)
  have tag (t : Nat) : PrimrecPred (fun p : A => p.2.2.2.1 = t) := Primrec.eq.comp htag (Primrec.const t)
  exact Primrec.ite (tag 0) heq (Primrec.ite (tag 1) hle (Primrec.ite (tag 2) hlt
    (Primrec.ite (tag 3) hneg (Primrec.ite (tag 4) hconj hdisj))))

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BooleanMatrix
