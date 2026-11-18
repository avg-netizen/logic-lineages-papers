module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Targets
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.ProgramsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeProgramsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.MachineLeastProgramsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.ProgramsProof
open OrdinalComparison PolynomialGraphCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair Computable Partrec
  ClosedWordDecisionCompletion.Machine.solve

 theorem blockRows_primitive : Primrec Code.blockRows := by
  have ha : Primrec (fun b : BlockCode =>
      ExpressionCode.run (ExpressionCode.instructions b.2.1) (b.1,[],[])) :=
    ExpressionCodeProgramsProof.run_primitive.comp
      (ExpressionCodeProgramsProof.instructions_primitive.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.pair ((Primrec.const []).pair (Primrec.const [])))
  exact Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp ha))
    (Primrec.list_cons.comp
      (ExpressionCodeProgramsProof.variableRow_primitive.comp (Primrec.snd.comp Primrec.snd)
        ((PolynomialBoolean.ProgramsProof.head_primitive 0).comp (Primrec.fst.comp (Primrec.snd.comp ha))))
      (Primrec.const []))

 theorem blockHeads_primitive : Primrec Code.blockHeads :=
  ExpressionCodeProgramsProof.headNames_primitive.comp
    (ExpressionCodeProgramsProof.instructions_primitive.comp (Primrec.fst.comp Primrec.snd))

 theorem decode_primitive : Primrec Code.decode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ([],[],[],0))

 theorem package_primitive : Primrec (fun x : Nat × Nat => Code.package x.1 x.2) := by
  have hq := decode_primitive.comp (Primrec.snd : Primrec (fun x : Nat × Nat => x.2))
  have hh := Primrec.fst.comp hq
  have hb := Primrec.fst.comp (Primrec.snd.comp hq)
  have hr := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hq))
  have hp := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hq))
  have hhead : Primrec (fun x : Nat × Nat => (Code.decode x.2).1.map Prod.fst) :=
    Primrec.list_map hh (Primrec.fst.comp Primrec.snd).to₂
  have hbhead : Primrec (fun x : Nat × Nat => (Code.decode x.2).2.1.flatMap Code.blockHeads) :=
    Primrec.list_flatMap hb (blockHeads_primitive.comp Primrec.snd).to₂
  have hd := HeadProgramsProof.familyDegree_primitive.comp (Primrec.list_append.comp hhead hbhead)
  have hhr : Primrec (fun x : Nat × Nat =>
      (Code.decode x.2).1.map (fun h => headEquation h.1 h.2.1 h.2.2)) :=
    Primrec.list_map hh (HeadProgramsProof.headEquation_primitive.comp Primrec.snd).to₂
  have hbr : Primrec (fun x : Nat × Nat => (Code.decode x.2).2.1.flatMap Code.blockRows) :=
    Primrec.list_flatMap hb (blockRows_primitive.comp Primrec.snd).to₂
  have hrows := Primrec.list_append.comp (Primrec.list_append.comp hhr hbr) hr
  exact hd.pair (PolynomialBoolean.ProgramsProof.conj_primitive.comp
    (PolynomialBoolean.ProgramsProof.positive_primitive.comp Primrec.fst)
    (PolynomialBoolean.ProgramsProof.conj_primitive.comp
      (PolynomialBoolean.ProgramsProof.graph_primitive.comp hrows) hp))

 def step (s : Nat × List BlockCode) (x : Nat × Nat) : Nat × List BlockCode :=
  (s.1+(ExpressionCode.instructions x.1).length,s.2++[(s.1,x.1,x.2)])

 theorem step_primitive : Primrec₂ step := by
  have hn : Primrec (fun p : (Nat × List BlockCode) × (Nat × Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hp : Primrec (fun p : (Nat × List BlockCode) × (Nat × Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun p : (Nat × List BlockCode) × (Nat × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : (Nat × List BlockCode) × (Nat × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (Primrec.nat_add.comp hn (Primrec.list_length.comp
    (ExpressionCodeProgramsProof.instructions_primitive.comp hc))).pair
    (Primrec.list_append.comp hp (Primrec.list_cons.comp (hn.pair (hc.pair hr)) (Primrec.const [])))

 theorem fold_allocate (xs : List (Nat × Nat)) (start : Nat) (prior : List BlockCode) :
    (xs.foldl step (start,prior)).2 = prior ++ Code.allocate start xs := by
  induction xs generalizing start prior with
  | nil => simp [Code.allocate]
  | cons x xs ih =>
    simp only [List.foldl_cons,step]
    rw [ih]
    simp [Code.allocate,List.append_assoc]

 theorem allocate_primitive : Primrec (fun x : Nat × List (Nat × Nat) => Code.allocate x.1 x.2) := by
  have hf : Primrec (fun x : Nat × List (Nat × Nat) => x.2.foldl step (x.1,[])) :=
    Primrec.list_foldl Primrec.snd (Primrec.fst.pair (Primrec.const []))
      (step_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.snd.comp hf).of_eq
  intro x
  simpa only [List.nil_append] using fold_allocate x.2 x.1 []

attribute [local irreducible] Code.package

 theorem full : Targets.Programs := by
  have hp := package_primitive.to_comp
  refine ⟨hp,?_,allocate_primitive.to_comp⟩
  exact ClosedWordDecisionCompletion.MachinePrograms.solve_computable.comp
    ((Computable.fst.comp hp).pair (Computable.snd.comp hp))
end LogicLineages.StandardControlCurrent.GraphNetwork.ProgramsProof
