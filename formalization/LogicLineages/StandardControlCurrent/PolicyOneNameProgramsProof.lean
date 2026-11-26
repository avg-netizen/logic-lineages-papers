module
public import LogicLineages.StandardControlCurrent.PolicyOneNameCompilationProof
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityPrograms
public import LogicLineages.OrdinalComparison.OneInputBooleanProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyOneName.Proof
open OrdinalComparison Source Source.ForwardTranslation

attribute [local irreducible] PolicySourceEquality.compileSyntax normalizeQuerySyntaxCode
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

theorem atom_program (policy : Source.AdmissibleSum.Policy) (hp : PolicyShape.Effective policy) : Computable (fun p : Nat × Nat × Nat => encodedOneNameSourceAtomProgram policy p.1 p.2.1 p.2.2) := by
  have hc : Computable (fun p : Nat × Nat × Nat => (1,p.2.1,p.2.2)) :=
    (Computable.const 1).pair Computable.snd
  have hs := (PolicySourceEqualityPrograms.compile policy hp).comp hc
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
  cases PolicySourceEquality.compileSyntax policy 1 p.2.1 p.2.2 <;> rfl

private theorem instruction_program (policy : Source.AdmissibleSum.Policy) (hp : PolicyShape.Effective policy) : Computable (fun instruction : OneInputBooleanInstruction =>
    if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
      encodedOneNameSourceAtomProgram policy (instruction.1-2) instruction.2.1 instruction.2.2
    else [instruction]) := by
  have htag : Primrec (fun p : OneInputBooleanInstruction => p.1) := Primrec.fst
  have hguard := (Primrec.nat_le.comp (Primrec.const 2) htag).and (Primrec.nat_le.comp htag (Primrec.const 4))
  have hparams := (Primrec.nat_sub.comp htag (Primrec.const 2)).pair Primrec.snd
  have hsingle : Primrec (fun instruction : OneInputBooleanInstruction => [instruction]) :=
    Primrec.list_cons.comp Primrec.id (Primrec.const [])
  simpa only [Bool.cond_decide] using
    Computable.cond hguard.decide.to_comp ((atom_program policy hp).comp hparams.to_comp) hsingle.to_comp

theorem program_computable (policy : Source.AdmissibleSum.Policy) (hp : PolicyShape.Effective policy) : Computable (encodedOneNameSourceBooleanProgram policy) := by
  have hs : Computable₂ (fun (_ : List OneInputBooleanInstruction) =>
      fun state : OneInputBooleanInstruction × List OneInputBooleanInstruction =>
      (if 2 ≤ state.1.1 ∧ state.1.1 ≤ 4 then
        encodedOneNameSourceAtomProgram policy (state.1.1-2) state.1.2.1 state.1.2.2
      else [state.1])++state.2) :=
    Computable.list_append.comp
      ((instruction_program policy hp).comp (Computable.fst.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr (0,0,0) Computable.id (Computable.const []) hs).of_eq
  intro program
  unfold encodedOneNameSourceBooleanProgram
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [id_eq,List.foldr_cons,List.flatMap_cons]
    apply congrArg (fun out : List OneInputBooleanInstruction =>
      (if 2 ≤ instruction.1 ∧ instruction.1 ≤ 4 then
        encodedOneNameSourceAtomProgram policy (instruction.1-2) instruction.2.1 instruction.2.2
      else [instruction])++out)
    simpa only [id_eq] using ih

theorem value_program (policy : Source.AdmissibleSum.Policy) (hp : PolicyShape.Effective policy) : Computable₂ (encodedOneNameSourceBooleanValue policy) := by
  apply (OneInputBoolean.value_program.comp ((program_computable policy hp).comp Computable.fst) Computable.snd).of_eq
  intro p
  unfold encodedOneNameSourceBooleanValue
  rfl

theorem closures_program (policy : Source.AdmissibleSum.Policy) (hp : PolicyShape.Effective policy) : Computable (encodedOneNameSourceBooleanClosures policy) := by
  apply (OneInputBoolean.closures_program.comp (program_computable policy hp)).of_eq
  intro program
  unfold encodedOneNameSourceBooleanClosures
  rfl

theorem programs : PolicyOneNameTargets.Programs := by
  intro p hp
  exact ⟨program_computable p hp,value_program p hp,closures_program p hp⟩
end LogicLineages.StandardControlCurrent.PolicyOneName.Proof
