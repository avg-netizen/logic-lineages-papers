module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.LeastFuelProgramsProof
private import LogicLineages.OrdinalComparison.OuterShiftNormalization.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerProgramsProof
open PolynomialGraphCompletion GuardChildMeasureCompletion OuterShiftNormalization
open ComparisonProgramsProof RunnerProgramsProof

theorem terminalRow_primitive : Primrec terminalRow := by
  have hempty : PrimrecPred (fun p : WordPair => coreWord p.1 = []) :=
    Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.fst)
      (Primrec.const [])
  have hr : Primrec (fun p : WordPair =>
      ((shiftSum p.1,[(1,0,[]),(-1,1,p.2)]) : Row)) :=
    (OuterShiftNormalization.Proof.shiftSum_primitive.comp Primrec.fst).pair
      (Primrec.list_cons.comp (Primrec.const ((1,0,[]) : Int × Nat × Word))
        (Primrec.list_cons.comp
          ((Primrec.const (-1 : Int)).pair ((Primrec.const 1).pair Primrec.snd))
          (Primrec.const [])))
  exact Primrec.ite hempty hr (Primrec.const ((1,[]) : Row))

theorem terminalTail_primitive : Primrec terminalTail := by
  have hA : PrimrecPred (fun p : WordPair => coreWord p.1 = []) :=
    Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.fst)
      (Primrec.const [])
  have hB : PrimrecPred (fun p : WordPair => coreWord p.2 = []) :=
    Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.snd)
      (Primrec.const [])
  exact Primrec.nat_max.comp OuterShiftNormalization.Proof.leafPairTail_primitive
    (Primrec.ite hA
      (Primrec.ite hB (Primrec.const 0)
        (OuterShiftNormalization.Proof.nonlinearLeafTail_primitive.comp
          (Primrec.snd.pair Primrec.fst)))
      OuterShiftNormalization.Proof.nonlinearLeafTail_primitive)

theorem terminalSame_primitive : Primrec terminalSame := by
  have hA : PrimrecPred (fun p : WordPair => coreWord p.1 = []) :=
    Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.fst)
      (Primrec.const [])
  have hB : PrimrecPred (fun p : WordPair => coreWord p.2 = []) :=
    Primrec.eq.comp (OuterShiftNormalization.Proof.coreWord_primitive.comp Primrec.snd)
      (Primrec.const [])
  exact Primrec.ite hA
    (Primrec.ite hB
      (orderInt_primitive.comp
        (OuterShiftNormalization.Proof.shiftSum_primitive.comp Primrec.fst)
        (OuterShiftNormalization.Proof.shiftSum_primitive.comp Primrec.snd))
      (Primrec.const 0))
    (Primrec.const 2)

theorem finiteTrace_primitive :
    Primrec (fun p : WordPair × Nat => finiteTrace p.1 p.2) :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    (Primrec.fst.comp (run_primitive.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂

theorem finish_primitive : Primrec (fun p : WordPair × Nat => finish p.1 p.2) := by
  have hp := Primrec.fst.comp run_primitive
  have htie := Primrec.snd.comp (Primrec.snd.comp run_primitive)
  have htail := Primrec.nat_max.comp (paidTail_primitive.comp run_primitive)
    (terminalTail_primitive.comp hp)
  have hrow := terminalRow_primitive.comp hp
  have hguards := makeGuards_primitive.comp htie
  have hsame := liftTie_primitive.comp htie (terminalSame_primitive.comp hp)
  exact htail.pair (hrow.pair (hguards.pair (hsame.pair finiteTrace_primitive)))

theorem boundedCompilerPrograms : Targets.BoundedCompilerPrograms :=
  ⟨signFormula_primitive, makeGuards_primitive, guardAt_primitive,
    terminalRow_primitive, terminalTail_primitive, terminalSame_primitive,
    finiteTrace_primitive, finish_primitive⟩

attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt compile leastFuel finish

theorem compile_computable :
    Computable (fun p : Nat × WordPair => compile p.1 p.2) := by
  have hf : Computable (fun q : WordPair × Nat => finish q.1 q.2) :=
    finish_primitive.to_comp
  have hargs : Computable (fun p : Nat × WordPair => (p.2,leastFuel p.1 p.2)) :=
    Computable.snd.pair LeastFuelProgramsProof.leastFuel_computable
  have hsuccess : Computable (fun p : Nat × WordPair => finish p.2 (leastFuel p.1 p.2)) :=
    Computable.comp (f := fun q : WordPair × Nat => finish q.1 q.2)
      (g := fun p : Nat × WordPair => (p.2,leastFuel p.1 p.2)) hf hargs
  apply (Computable.cond admitted_primitive.to_comp hsuccess
    (Computable.const invalidPackage)).of_eq
  intro p
  unfold compile
  cases h : admitted p.1 p.2 <;> simp [h]

theorem compilerProgram : Targets.CompilerProgram := compile_computable

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerProgramsProof
