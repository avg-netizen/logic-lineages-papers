module
public import LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedElementaryProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

theorem equalRankWordGuardPrograms : Targets.EqualRankWordGuardPrograms := by
  let P := Word × Word × Nat × Nat × Nat × Int × Int
  have hA : Primrec (fun p : P => p.1) := Primrec.fst
  have hB : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have hT : Primrec (fun p : P => equalityTail p.2.2.1 p.2.2.2.1
      p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) :=
    Focused.uniformTailPrograms.2.2.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_max.comp
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hA.pair hT))
    (WordGuardCompletion.Proof.reachTail_primitive.comp (hB.pair hT))

end LogicLineages.OrdinalComparison.EqualRankWordGuardCompletion.Proof
