module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerDataProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
open PolynomialGraphCompletion Algorithm AlgorithmPrograms
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

theorem step_computable :
    Computable (fun p : Nat × Nat × Runner.EncodedState => step p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Runner.EncodedState
  have hstate : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hhead := Primrec.list_head?.to_comp.comp (Computable.fst.comp (Computable.snd.comp hstate))
  have hs : Computable (fun p : A × WorkData => p.1.2.2) := hstate.comp Computable.fst
  have hbs : Computable (fun p : A × WorkData =>
      (stage p.1.1 p.1.2.1 p.2.1).map encodeBranch) :=
    AlgorithmPrograms.actualStageProgram.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd)))
  have hbwork : Computable (fun p : WorkData × EncodedBranch => branchWork p.1 p.2) :=
    branchWork_primitive.to_comp
  have hbfinished : Computable (fun p : WorkData × EncodedBranch => branchFinished p.1 p.2) :=
    branchFinished_primitive.to_comp
  have hcwork := computable_filterMap ((0,0,0,0,((0 : Int),[])) : EncodedBranch) hbs
    (hbwork.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  have hcfinished := computable_filterMap ((0,0,0,0,((0 : Int),[])) : EncodedBranch) hbs
    (hbfinished.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂
  have htails : Computable (fun p : A × WorkData =>
      ((stage p.1.1 p.1.2.1 p.2.1).map encodeBranch).map Prod.fst) :=
    computable_map ((0,0,0,0,((0 : Int),[])) : EncodedBranch) hbs
      (Computable.fst.comp Computable.snd).to₂
  have hpaid := Primrec.nat_max.to_comp.comp (Computable.fst.comp hs)
    (foldMax_primitive.to_comp.comp htails)
  have hrest := Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp hs))
  have hfinished := Computable.snd.comp (Computable.snd.comp hs)
  have hsome : Computable₂ (fun p : A => fun parent : WorkData =>
      let bs := (stage p.1 p.2.1 parent.1).map encodeBranch
      ((max p.2.2.1 (foldMax (bs.map Prod.fst)),
        bs.filterMap (branchWork parent)++p.2.2.2.1.tail,
        bs.filterMap (branchFinished parent)++p.2.2.2.2) : Runner.EncodedState)) :=
    (hpaid.pair ((Computable.list_append.comp hcwork hrest).pair
      (Computable.list_append.comp hcfinished hfinished))).to₂
  apply (Computable.option_casesOn hhead hstate hsome).of_eq
  intro p
  rcases p with ⟨D,maximum,paid,work,finished⟩
  cases work <;> rfl

theorem run_computable :
    Computable (fun p : Nat × Nat × Row × Nat => run p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Nat × Row × Nat
  have hD : Computable (fun p : A => p.1) := Computable.fst
  have hm : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hr : Computable (fun p : A => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hf : Computable (fun p : A => p.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hstep : Computable₂ (fun p : A => fun state : Nat × Runner.EncodedState =>
      step p.1 p.2.1 state.2) :=
    step_computable.comp ((hD.comp Computable.fst).pair
      ((hm.comp Computable.fst).pair (Computable.snd.comp Computable.snd)))
  apply (Computable.nat_rec hf (initial_primitive.to_comp.comp hr) hstep).of_eq
  intro p
  change Nat.rec (initial p.2.2.1) (fun _ state => step p.1 p.2.1 state) p.2.2.2 =
    (step p.1 p.2.1)^[p.2.2.2] (initial p.2.2.1)
  induction p.2.2.2 with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply'] using congrArg (step p.1 p.2.1) ih

theorem finiteRunnerProgram : RunnerTargets.FiniteRunnerProgram := by
  apply run_computable.of_eq
  intro p
  exact run_calibration p.1 p.2.1 p.2.2.1 p.2.2.2

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerCode
