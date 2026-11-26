module
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoTargets
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCodeProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionCodeProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.NumericProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum LevelTwoCounterexample SourceCode
attribute [local irreducible] PolicySourceInterface.compile PolicyLevelTwo.compile
  PolicyLevelTwo.admittedCompile PolicyLevelTwo.decision PolicyLevelTwo.solve
  LevelTwoDecisionCompletion.packageCounterexample
theorem compile_program (policy : Policy) (hp : PolicyShape.Effective policy) : Computable (PolicyLevelTwo.compile policy) := by
  have ha : Computable (fun p : Input => PolicySourceInterface.compile policy p.1 p.2.2.1) :=
    Computable.comp (f := fun x : Nat × Nat => PolicySourceInterface.compile policy x.1 x.2)
      (g := fun q : Input => (q.1,q.2.2.1)) (PolicySourceInterfaceProof.programs.1 policy hp)
      (Computable.fst.pair (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hb : Computable (fun p : Input => PolicySourceInterface.compile policy p.1 p.2.2.2) :=
    Computable.comp (f := fun x : Nat × Nat => PolicySourceInterface.compile policy x.1 x.2)
      (g := fun q : Input => (q.1,q.2.2.2)) (PolicySourceInterfaceProof.programs.1 policy hp)
      (Computable.fst.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  let A := (Input × EncodedVector) × EncodedVector
  have hp : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hn : Primrec (fun p : A => p.1.1.1) := Primrec.fst.comp hp
  have hm : Primrec (fun p : A => p.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp hp)
  have hav : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hbv : Primrec (fun p : A => p.2) := Primrec.snd
  have hf := SourceCodeProof.positiveFlag_primitive.comp (hm.pair (hav.pair hbv))
  have hla := ScalarCodeProof.actualNumericPrograms.2.1.comp (Primrec.fst.comp hav)
  have hlb := ScalarCodeProof.actualNumericPrograms.2.1.comp (Primrec.fst.comp hbv)
  have hout := PairCodeProof.actualNumericProgram.comp (hn.pair (hm.pair (hf.pair (hla.pair hlb))))
  unfold PolicyLevelTwo.compile
  exact Computable.option_bind ha
    (Computable.option_bind (hb.comp Computable.fst) (Computable.option_some.comp hout.to_comp).to₂).to₂

theorem admitted_program (policy : Policy) (hp : PolicyShape.Effective policy) :
    Computable (PolicyLevelTwo.admittedCompile policy) := by
  exact (Computable.cond AdmissionCodeProof.accepts_primitive.to_comp
    (compile_program policy hp) (Computable.const none)).of_eq (fun q => by
      simp only [PolicyLevelTwo.admittedCompile,Bool.cond_eq_ite])

theorem decision_program (policy : Policy) (hp : PolicyShape.Effective policy) :
    Computable (PolicyLevelTwo.decision policy) := by
  have h : Computable₂ (fun _ : Input => fun pack : Pair.Package =>
      !(LevelTwoDecisionCompletion.packageCounterexample pack)) :=
    Primrec.not.to_comp.comp (LevelTwoDecisionCompletion.ProgramsProof.packageCounterexample_computable.comp Computable.snd)
  unfold PolicyLevelTwo.decision
  exact Computable.option_map (admitted_program policy hp) h

theorem programs : PolicyLevelTwoTargets.Programs := by
  intro p hp
  refine ⟨compile_program p hp,admitted_program p hp,decision_program p hp,?_⟩
  unfold PolicyLevelTwo.solve
  exact Computable.option_getD (decision_program p hp) (Computable.const false)
end LogicLineages.StandardControlCurrent.PolicyLevelTwoProof
