module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodeDataProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem lowerRow_primitive : Primrec₂ lowerRow := by
  have hc : Primrec (fun p : Nat × Nat => -(p.1 : Int)) :=
    LayeredComparison.IntegerAlgorithms.Proof.negate_primitive.comp
      (LayeredComparison.IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.fst)
  have hi : Primrec (fun p : Nat × Nat => ((1 : Int),(p.2,([] : Word)))) :=
    (Primrec.const (1 : Int)).pair (Primrec.snd.pair (Primrec.const ([] : Word)))
  exact hc.pair (Primrec.list_cons.comp hi (Primrec.const []))

theorem maximumRow_primitive : Primrec₂ maximumRow := by
  have hl : Primrec (fun p : Nat × Nat => ((1 : Int),(p.1,([] : Word)))) :=
    (Primrec.const (1 : Int)).pair (Primrec.fst.pair (Primrec.const ([] : Word)))
  have hr : Primrec (fun p : Nat × Nat => ((-1 : Int),(p.2,([] : Word)))) :=
    (Primrec.const (-1 : Int)).pair (Primrec.snd.pair (Primrec.const ([] : Word)))
  exact (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const [])))

theorem nonnegative_primitive : Primrec Code.nonnegative :=
  AlgorithmPrograms.nonnegative_encode_primitive

theorem frame_primitive : Primrec (fun p : Nat × Nat × List Nat =>
    Code.frame p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List Nat
  have hN : Primrec (fun p : A × (Nat × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun p : A × (Nat × Nat) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun p : A × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : A × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlower := nonnegative_primitive.comp (lowerRow_primitive.comp hN hi)
  have hupper := nonnegative_primitive.comp (maximumRow_primitive.comp hm hi)
  have hstep : Primrec₂ (fun p : A => fun w : Nat × Nat =>
      LinearRows.Code.conjunction (Code.nonnegative (lowerRow p.1 w.1))
        (LinearRows.Code.conjunction (Code.nonnegative (maximumRow p.2.1 w.1)) w.2)) :=
    AlgorithmPrograms.conjunction_encode_primitive.comp hlower
      (AlgorithmPrograms.conjunction_encode_primitive.comp hupper hs)
  exact Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const 0) hstep

#print axioms lowerRow_primitive
#print axioms maximumRow_primitive
#print axioms nonnegative_primitive
#print axioms frame_primitive

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
