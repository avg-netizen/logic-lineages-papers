module
public import LogicLineages.OrdinalComparison.OneNameSourceCompilationProof
public import LogicLineages.OrdinalComparison.OneInputBooleanProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneNameSourceBoolean
open Source Source.ForwardTranslation

attribute [local irreducible] OriginalInput.compileSyntax normalizeQuerySyntaxCode
  encodedOneNameSourceAtomProgram encodedOneNameSourceBooleanProgram
  encodedOneNameSourceBooleanValue encodedOneNameSourceBooleanClosures
  encodedOneInputBooleanValue encodedOneInputBooleanClosures

theorem guard_program : Primrec (fun p : Nat × EncodedQuery => encodedOneNameSourceGuard p.1 p.2) := by
  have hv := Primrec.snd.comp (Primrec.snd : Primrec (fun p : Nat × EncodedQuery => p.2))
  have ha := Primrec.snd.comp (Primrec.fst.comp hv)
  have hb := Primrec.snd.comp (Primrec.snd.comp hv)
  have hle := positiveComparisonPrimitiveRecursive.comp ha hb
  have hrev := positiveComparisonPrimitiveRecursive.comp hb ha
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.and.comp hle hrev) hle

theorem atom_program : Computable (fun p : Nat × Nat × Nat => encodedOneNameSourceAtomProgram p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Nat × Nat × Nat => (1,false,p.2.1,p.2.2)) :=
    (Primrec.const 1).pair ((Primrec.const false).pair Primrec.snd)
  have hs := (OriginalInput.compileSyntaxPrimitiveRecursive.comp hc).to_comp
  have hnorm := querySyntaxNormalizationPrimitiveRecursive.comp
    (Primrec.snd : Primrec (fun p : (Nat × Nat × Nat) × EncodedQuery => p.2))
  have hr := Primrec.fst.comp (Primrec.fst : Primrec (fun p : (Nat × Nat × Nat) × EncodedQuery => p.1))
  have hg := guard_program.comp (hr.pair hnorm)
  have hflag := Primrec.cond hg (Primrec.const 1) (Primrec.const 0)
  have ha := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp hnorm))
  have hb := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hnorm))
  have hfirst : Primrec (fun p : (Nat × Nat × Nat) × EncodedQuery =>
      (if encodedOneNameSourceGuard p.1.1 (normalizeQuerySyntaxCode p.2) then 1 else 0,0,0)) := by
    apply (hflag.pair (Primrec.const (0,0))).of_eq
    intro p
    cases encodedOneNameSourceGuard p.1.1 (normalizeQuerySyntaxCode p.2) <;> rfl
  have hsecond := (Primrec.nat_add.comp (Primrec.const 2) hr).pair (ha.pair hb)
  have hp : Primrec₂ (fun p : Nat × Nat × Nat => fun syn : EncodedQuery =>
      [(if encodedOneNameSourceGuard p.1 (normalizeQuerySyntaxCode syn) then 1 else 0,0,0),
        (2+p.1,(normalizeQuerySyntaxCode syn).2.1.1,(normalizeQuerySyntaxCode syn).2.2.1),(6,0,0)]) :=
    Primrec.list_cons.comp hfirst (Primrec.list_cons.comp hsecond
      (Primrec.list_cons.comp (Primrec.const (6,0,0)) (Primrec.const [])))
  apply (Computable.option_casesOn hs (Computable.const [(0,0,0)]) hp.to_comp).of_eq
  intro p
  unfold encodedOneNameSourceAtomProgram
  cases OriginalInput.compileSyntax (1,false,p.2.1,p.2.2) <;> rfl

private theorem instruction_program : Computable (fun instruction : OneInputBooleanInstruction =>
    if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
      encodedOneNameSourceAtomProgram (instruction.1-2) instruction.2.1 instruction.2.2
    else [instruction]) := by
  have htag : Primrec (fun p : OneInputBooleanInstruction => p.1) := Primrec.fst
  have hguard := (Primrec.nat_le.comp (Primrec.const 2) htag).and (Primrec.nat_le.comp htag (Primrec.const 4))
  have hparams := (Primrec.nat_sub.comp htag (Primrec.const 2)).pair Primrec.snd
  have hsingle : Primrec (fun instruction : OneInputBooleanInstruction => [instruction]) :=
    Primrec.list_cons.comp Primrec.id (Primrec.const [])
  simpa only [Bool.cond_decide] using
    Computable.cond hguard.decide.to_comp (atom_program.comp hparams.to_comp) hsingle.to_comp

theorem program_computable : Computable encodedOneNameSourceBooleanProgram := by
  have hs : Computable₂ (fun (_ : List OneInputBooleanInstruction) =>
      fun state : OneInputBooleanInstruction × List OneInputBooleanInstruction =>
      (if 2 ≤ state.1.1 ∧ state.1.1 ≤ 4 then
        encodedOneNameSourceAtomProgram (state.1.1-2) state.1.2.1 state.1.2.2
      else [state.1])++state.2) :=
    Computable.list_append.comp
      (instruction_program.comp (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr (0,0,0) Computable.id (Computable.const []) hs).of_eq
  intro program
  unfold encodedOneNameSourceBooleanProgram
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [id_eq,List.foldr_cons,List.flatMap_cons]
    apply congrArg (fun out : List OneInputBooleanInstruction =>
      (if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
        encodedOneNameSourceAtomProgram (instruction.1-2) instruction.2.1 instruction.2.2
      else [instruction])++out)
    simpa only [id_eq] using ih

theorem value_program : Computable₂ encodedOneNameSourceBooleanValue := by
  apply (OneInputBoolean.value_program.comp (program_computable.comp Computable.fst) Computable.snd).of_eq
  intro p
  unfold encodedOneNameSourceBooleanValue
  rfl

theorem closures_program : Computable encodedOneNameSourceBooleanClosures := by
  apply (OneInputBoolean.closures_program.comp program_computable).of_eq
  intro program
  unfold encodedOneNameSourceBooleanClosures
  rfl

theorem programs : Targets.ActualOneNameSourceBooleanPrograms := ⟨program_computable,value_program,closures_program⟩

end LogicLineages.OrdinalComparison.OneNameSourceBoolean
