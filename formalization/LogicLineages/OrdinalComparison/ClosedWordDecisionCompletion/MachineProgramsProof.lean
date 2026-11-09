module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ConstantLeafProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachinePrograms
open Machine RankedWordDecisionCompletion
attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt

theorem initial_primitive : Primrec (fun p : Nat × Nat × Nat => initial p.1 p.2.1 p.2.2) :=
  (Primrec.const false).pair (Primrec.list_cons.comp Primrec.id (Primrec.const []))

theorem step_computable : Computable (fun p : Nat × State => step p.1 p.2) := by
  let A := Nat × State
  have hwork : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hhead := Primrec.list_head?.to_comp.comp hwork
  have hrest : Computable (fun p : A × Work => p.1.2.2.tail) :=
    Primrec.list_tail.to_comp.comp (hwork.comp Computable.fst)
  have hfuel : Computable (fun p : A × Work => p.2.1) := Computable.fst.comp Computable.snd
  have hfloor : Computable (fun p : A × Work => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcode : Computable (fun p : A × Work => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hchildren := CodePrograms.children_computable.comp
    ((Computable.fst.comp Computable.fst).pair (hfloor.pair hcode))
  have hchild : Computable₂ (fun p : A × Work => fun b : Nat × Nat => (p.2.1-1,b.1,b.2)) :=
    (Primrec.nat_sub.to_comp.comp (hfuel.comp Computable.fst) (Computable.const 1)).pair Computable.snd
  have hexpanded := AlgorithmPrograms.computable_map (0,0) hchildren hchild
  have hlarge := (Computable.const false).pair (Primrec.list_append.to_comp.comp hexpanded hrest)
  have hzero := (Computable.const false).pair hrest
  have hconstant := (ConstantLeafProof.constant_primitive.to_comp.comp hcode).pair hrest
  have hsome := Computable.cond
    (Primrec.beq.to_comp.comp (CodePrograms.names_primitive.to_comp.comp hcode) (Computable.const []))
    hconstant (Computable.cond
      (Primrec.beq.to_comp.comp hfuel (Computable.const 0)) hzero hlarge)
  have hbody := Computable.option_casesOn hhead Computable.snd hsome.to₂
  apply (Computable.cond (Computable.fst.comp Computable.snd) Computable.snd hbody).of_eq
  intro p
  rcases p with ⟨D,flag,work⟩
  cases flag
  · cases work with
    | nil => rfl
    | cons w rest =>
      rcases w with ⟨fuel,floor,code⟩
      by_cases hn : Code.names code = [] <;> by_cases hf : fuel = 0 <;>
        simp [step,Bool.cond_eq_ite,hn,hf]
  · rfl

theorem run_computable : Computable (fun p : Nat × Nat × Nat × Nat × Nat =>
    run p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let A := Nat × Nat × Nat × Nat × Nat
  have hfuel : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hfloor : Computable (fun p : A => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcode : Computable (fun p : A => p.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hsteps : Computable (fun p : A => p.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hi := initial_primitive.to_comp.comp (hfuel.pair (hfloor.pair hcode))
  have hs : Computable₂ (fun p : A => fun s : Nat × State => step p.1 s.2) :=
    step_computable.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp Computable.snd))
  apply (Computable.nat_rec hsteps hi hs).of_eq
  intro p
  change Nat.rec (initial p.2.1 p.2.2.1 p.2.2.2.1) (fun _ s => step p.1 s) p.2.2.2.2 =
    (step p.1)^[p.2.2.2.2] (initial p.2.1 p.2.2.1 p.2.2.2.1)
  induction p.2.2.2.2 with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply'] using congrArg (step p.1) ih

theorem actualTransitionPrograms : MachineTargets.ActualTransitionPrograms :=
  ⟨ConstantLeafProof.constant_primitive,step_computable,run_computable⟩

#print axioms initial_primitive
#print axioms step_computable
#print axioms run_computable
#print axioms actualTransitionPrograms

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachinePrograms
