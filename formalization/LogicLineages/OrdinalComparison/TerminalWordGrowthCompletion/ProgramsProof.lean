module
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Targets
public import LogicLineages.OrdinalComparison.WordGuardCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem growthOffset_primitive : Primrec growthOffset :=
  Primrec.nat_add.comp WordGuardCompletion.Proof.wordOffset_primitive
    (Primrec.const 1)

theorem growthTail_primitive : Primrec growthTail :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp WordGuardCompletion.Proof.wordTail_primitive
      (Primrec.nat_mul.comp (Primrec.const 2)
        WordGuardCompletion.Proof.wordOffset_primitive))
    (Primrec.const 2)

theorem terminalTail_primitive : Primrec
    (fun p : Word × Int => terminalTail p.1 p.2) :=
  Primrec.nat_max.comp (growthTail_primitive.comp Primrec.fst)
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (growthOffset_primitive.comp Primrec.fst))
        (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.snd))
      (Primrec.const 2))

theorem growthPrograms : Targets.GrowthPrograms :=
  ⟨growthOffset_primitive, growthTail_primitive, terminalTail_primitive⟩

end LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.Proof
