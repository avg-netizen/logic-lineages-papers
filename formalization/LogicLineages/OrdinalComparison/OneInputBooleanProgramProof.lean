module
public import LogicLineages.OrdinalComparison.OneInputBooleanValueProof
public import LogicLineages.OrdinalComparison.OneVariableSignSourceProof
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneInputBoolean

attribute [local irreducible] encodedPositiveEvaluation encodedOneVariableSignDecision
  encodedOneInputBooleanStep encodedOneInputBooleanRun encodedOneInputBooleanValue
  encodedOneInputBooleanInstructionTail encodedOneInputBooleanTail encodedOneInputBooleanClosures

private theorem computable_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

theorem order_program : Primrec (fun p : Nat × Nat × Nat => oneInputOrderBool p.1 p.2.1 p.2.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide
      (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).decide)

theorem step_program : Computable (fun p : Nat × OneInputBooleanInstruction × List Bool =>
    encodedOneInputBooleanStep p.1 p.2.1 p.2.2) := by
  have hx : Primrec (fun p : Nat × OneInputBooleanInstruction × List Bool => p.1) := Primrec.fst
  have hi : Primrec (fun p : Nat × OneInputBooleanInstruction × List Bool => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Nat × OneInputBooleanInstruction × List Bool => p.2.2) := Primrec.snd.comp Primrec.snd
  have htag := Primrec.fst.comp hi
  have ha := Primrec.fst.comp (Primrec.snd.comp hi)
  have hb := Primrec.snd.comp (Primrec.snd.comp hi)
  have hA := encodedPositiveEvaluationComputable.comp ha.to_comp hx.to_comp
  have hB := encodedPositiveEvaluationComputable.comp hb.to_comp hx.to_comp
  have hAtom := order_program.to_comp.comp
    ((Primrec.nat_sub.comp htag (Primrec.const 2)).to_comp.pair (hA.pair hB))
  have hHead := (Primrec.list_getD false).comp hs (Primrec.const 0)
  have hTail := Primrec.list_tail.comp hs
  have hSecond := (Primrec.list_getD false).comp hTail (Primrec.const 0)
  have hRest := Primrec.list_tail.comp hTail
  have hFalse := Primrec.list_cons.comp (Primrec.const false) hs
  have hTrue := Primrec.list_cons.comp (Primrec.const true) hs
  have hNeg := Primrec.list_cons.comp ((Primrec.dom_bool (fun b => !b)).comp hHead) hTail
  have hAnd := Primrec.list_cons.comp ((Primrec.dom_bool₂ (fun a b => a && b)).comp hSecond hHead) hRest
  have hOr := Primrec.list_cons.comp ((Primrec.dom_bool₂ (fun a b => a || b)).comp hSecond hHead) hRest
  have h := computable_ite (Primrec.eq.comp htag (Primrec.const 0)) hFalse.to_comp
    (computable_ite (Primrec.eq.comp htag (Primrec.const 1)) hTrue.to_comp
      (computable_ite (Primrec.nat_le.comp htag (Primrec.const 4))
        (Computable.list_cons.comp hAtom hs.to_comp)
        (computable_ite (Primrec.eq.comp htag (Primrec.const 5)) hNeg.to_comp
          (computable_ite (Primrec.eq.comp htag (Primrec.const 6)) hAnd.to_comp
            (computable_ite (Primrec.eq.comp htag (Primrec.const 7)) hOr.to_comp hFalse.to_comp)))))
  apply h.of_eq
  intro p
  unfold encodedOneInputBooleanStep
  simp only [List.headD_eq_getD]

theorem run_program : Computable (fun p : List OneInputBooleanInstruction × Nat × List Bool =>
    encodedOneInputBooleanRun p.1 p.2.1 p.2.2) := by
  have hx : Computable (fun p : (List OneInputBooleanInstruction × Nat × List Bool) × (List Bool × OneInputBooleanInstruction) =>
      p.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hi : Computable (fun p : (List OneInputBooleanInstruction × Nat × List Bool) × (List Bool × OneInputBooleanInstruction) =>
      p.2.2) := Computable.snd.comp Computable.snd
  have hs : Computable (fun p : (List OneInputBooleanInstruction × Nat × List Bool) × (List Bool × OneInputBooleanInstruction) =>
      p.2.1) := Computable.fst.comp Computable.snd
  have hstep : Computable₂ (fun p : List OneInputBooleanInstruction × Nat × List Bool =>
      fun state : List Bool × OneInputBooleanInstruction => encodedOneInputBooleanStep p.2.1 state.2 state.1) :=
    step_program.comp (hx.pair (hi.pair hs))
  apply (ComparisonAssembly.computable_foldl (0,0,0) Computable.fst
    (Computable.snd.comp Computable.snd) hstep).of_eq
  intro p
  unfold encodedOneInputBooleanRun
  rfl

theorem value_program : Computable₂ encodedOneInputBooleanValue := by
  have hr := run_program.comp (Computable.fst.pair (Computable.snd.pair (Computable.const [])))
  apply ((Primrec.list_getD false).to_comp.comp hr (Computable.const 0)).of_eq
  intro p
  unfold encodedOneInputBooleanValue
  exact List.headD_eq_getD.symm

theorem instruction_tail_program : Computable encodedOneInputBooleanInstructionTail := by
  have htag : Primrec (fun p : OneInputBooleanInstruction => p.1) := Primrec.fst
  have ha : Primrec (fun p : OneInputBooleanInstruction => 2*p.2.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : OneInputBooleanInstruction => 2*p.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
  have hcut := Computable.snd.comp (ComparisonAssembly.decision_program.comp ha.to_comp hb.to_comp)
  have h := computable_ite
    ((Primrec.nat_le.comp (Primrec.const 2) htag).and (Primrec.nat_le.comp htag (Primrec.const 4)))
    hcut (Computable.const 1)
  apply h.of_eq
  intro p
  unfold encodedOneInputBooleanInstructionTail
  rfl

theorem tail_program : Computable encodedOneInputBooleanTail := by
  have hs : Computable₂ (fun (_ : List OneInputBooleanInstruction) => fun state : OneInputBooleanInstruction × Nat =>
      max (encodedOneInputBooleanInstructionTail state.1) state.2) :=
    Primrec.nat_max.to_comp.comp
      (instruction_tail_program.comp (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr (0,0,0) Computable.id (Computable.const 1) hs).of_eq
  intro program
  unfold encodedOneInputBooleanTail
  induction program with
  | nil => rfl
  | cons instruction rest ih => simpa only [id_eq,List.foldr_cons,List.map_cons] using congrArg (max _) ih

private theorem any_program : Computable₂ (fun program : List OneInputBooleanInstruction => fun points : List Nat =>
    points.any (encodedOneInputBooleanValue program)) := by
  have hs : Computable₂ (fun p : List OneInputBooleanInstruction × List Nat => fun state : Nat × Bool =>
      encodedOneInputBooleanValue p.1 state.1 || state.2) :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp
      (value_program.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr 0 Computable.snd (Computable.const false) hs).of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons x rest ih => simp only [List.foldr_cons,List.any_cons]; rw [ih]

private theorem all_program : Computable₂ (fun program : List OneInputBooleanInstruction => fun points : List Nat =>
    points.all (encodedOneInputBooleanValue program)) := by
  have hs : Computable₂ (fun p : List OneInputBooleanInstruction × List Nat => fun state : Nat × Bool =>
      encodedOneInputBooleanValue p.1 state.1 && state.2) :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp
      (value_program.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr 0 Computable.snd (Computable.const true) hs).of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons x rest ih => simp only [List.foldr_cons,List.all_cons]; rw [ih]

theorem closures_program : Computable encodedOneInputBooleanClosures := by
  have hPoints : Computable (fun program : List OneInputBooleanInstruction =>
      ((List.range (encodedOneInputBooleanTail program+1)).drop 1)) :=
    Primrec.list_drop.to_comp.comp (Computable.const 1)
      (Primrec.list_range.to_comp.comp (Computable.succ.comp tail_program))
  apply ((any_program.comp Computable.id hPoints).pair (all_program.comp Computable.id hPoints)).of_eq
  intro program
  unfold encodedOneInputBooleanClosures
  rfl

theorem programs : Targets.ActualOneInputBooleanPrograms := ⟨value_program,tail_program,closures_program⟩

end LogicLineages.OrdinalComparison.OneInputBoolean
