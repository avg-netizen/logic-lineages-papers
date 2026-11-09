module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmBaseProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion Algorithm

theorem counterLetter_primitive : Primrec₂ counterLetter :=
  (Primrec.const 4).pair (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (0 : Int))))

theorem kernelLetter_zero_primitive : Primrec₂ (fun d c => kernelLetter d c 0) :=
  (Primrec.const 3).pair (Primrec.fst.pair (Primrec.snd.pair (Primrec.const (0 : Int))))

theorem prependResidual_primitive : Primrec (fun p : Letter × List (Nat × Word) =>
    p.2.map (fun q => (q.1,p.1::q.2))) := by
  have hi : Primrec (fun p : (Letter × List (Nat × Word)) × (Nat × Word) =>
      (p.2.1,p.1.1::p.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_map Primrec.snd hi.to₂

theorem residualWords_primitive : Primrec (fun p : Nat × Nat => residualWords p.1 p.2) := by
  let E := Nat × Word
  let A := Nat × Nat
  have hseed : Primrec (fun p : A => [(3,[counterLetter 3 (p.2+3)])]) :=
    Primrec.list_cons.comp
      ((Primrec.const 3).pair (Primrec.list_cons.comp
        (counterLetter_primitive.comp (Primrec.const 3)
          (Primrec.nat_add.comp Primrec.snd (Primrec.const 3))) (Primrec.const [])))
      (Primrec.const [])
  have hd : Primrec (fun p : A × (Nat × List E) => p.2.1+4) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 4)
  have hc : Primrec (fun p : A × (Nat × List E) => p.1.2+p.2.1+4) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)) (Primrec.const 4)
  have hfront := hd.pair (Primrec.list_cons.comp (counterLetter_primitive.comp hd hc) (Primrec.const []))
  have hrest := prependResidual_primitive.comp
    ((kernelLetter_zero_primitive.comp hd hc).pair (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ (fun p : A => fun state : Nat × List E =>
      (state.1+4,[counterLetter (state.1+4) (p.2+state.1+4)]) ::
        state.2.map (fun q => (q.1,kernelLetter (state.1+4) (p.2+state.1+4) 0 :: q.2))) :=
    Primrec.list_cons.comp hfront hrest
  apply (Primrec.nat_rec' Primrec.fst hseed hstep).of_eq
  intro p
  rcases p with ⟨n,c⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [residualWords] using congrArg
        (fun xs => (n+4,[counterLetter (n+4) (c+n+4)]) ::
          xs.map (fun q => (q.1,kernelLetter (n+4) (c+n+4) 0 :: q.2))) ih

theorem upperResidualWords_primitive :
    Primrec (fun p : Nat × Nat × Nat => upperResidualWords p.1 p.2.1 p.2.2) := by
  let E := Nat × Word
  let A := Nat × Nat × Nat
  have hd : Primrec (fun p : A × (Nat × List E) => p.1.2.1+p.2.1+4) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)) (Primrec.const 4)
  have hc : Primrec (fun p : A × (Nat × List E) => p.1.2.2+p.1.2.1+p.2.1+4) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp Primrec.snd)) (Primrec.const 4)
  have hfront := hd.pair (Primrec.list_cons.comp (counterLetter_primitive.comp hd hc) (Primrec.const []))
  have hrest := prependResidual_primitive.comp
    ((kernelLetter_zero_primitive.comp hd hc).pair (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ (fun p : A => fun state : Nat × List E =>
      (p.2.1+state.1+4,[counterLetter (p.2.1+state.1+4) (p.2.2+p.2.1+state.1+4)]) ::
        state.2.map (fun q => (q.1,kernelLetter (p.2.1+state.1+4) (p.2.2+p.2.1+state.1+4) 0 :: q.2))) :=
    Primrec.list_cons.comp hfront hrest
  apply (Primrec.nat_rec' Primrec.fst (Primrec.const ([] : List E)) hstep).of_eq
  intro p
  rcases p with ⟨k,m,c⟩
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [upperResidualWords] using congrArg
        (fun xs => (m+k+4,[counterLetter (m+k+4) (c+m+k+4)]) ::
          xs.map (fun q => (q.1,kernelLetter (m+k+4) (c+m+k+4) 0 :: q.2))) ih

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
