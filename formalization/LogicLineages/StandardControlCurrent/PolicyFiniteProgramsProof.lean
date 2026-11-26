module
public import LogicLineages.StandardControlCurrent.PolicyFiniteClassProof
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityPrograms
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum LevelTwoCounterexample
attribute [local irreducible] PolicySourceEquality.compileSyntax PolicyLevelTwo.compile
  PolicyFinite.accepts PolicyFinite.admittedCompile PolicyFinite.decision PolicyFinite.solve
  LevelTwoDecisionCompletion.packageCounterexample

theorem accepts_program (p : Policy) (hp : PolicyShape.Effective p) : Computable (PolicyFinite.accepts p) := by
  have hs : Computable (fun q : SourceCode.Input => PolicySourceEquality.compileSyntax p q.1 q.2.2.1 q.2.2.2) :=
    Computable.comp (f := fun x : Nat × Nat × Nat => PolicySourceEquality.compileSyntax p x.1 x.2.1 x.2.2)
      (g := fun q : SourceCode.Input => (q.1,q.2.2.1,q.2.2.2)) (PolicySourceEqualityPrograms.compile p hp)
      (Computable.fst.pair (Computable.snd.comp Computable.snd))
  have hf : Primrec₂ (fun _ : SourceCode.Input => fun syn : EncodedQuery =>
      PolicyFinite.finiteScalarCode syn.2.1.1 && PolicyFinite.finiteScalarCode syn.2.2.1) :=
    Primrec.and.comp
      (checker_primitive.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (checker_primitive.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  apply (Computable.option_getD (Computable.option_map hs hf.to_comp) (Computable.const false)).of_eq
  intro q
  unfold PolicyFinite.accepts
  cases PolicySourceEquality.compileSyntax p q.1 q.2.2.1 q.2.2.2 <;> rfl

theorem admitted_program (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (PolicyFinite.admittedCompile p) := by
  exact (Computable.cond (accepts_program p hp) (PolicyLevelTwoProof.compile_program p hp)
    (Computable.const none)).of_eq (fun q => by simp only [PolicyFinite.admittedCompile,Bool.cond_eq_ite])

theorem decision_program (p : Policy) (hp : PolicyShape.Effective p) : Computable (PolicyFinite.decision p) := by
  unfold PolicyFinite.decision
  exact Computable.option_map (admitted_program p hp)
    (Primrec.not.to_comp.comp (LevelTwoDecisionCompletion.ProgramsProof.packageCounterexample_computable.comp Computable.snd)).to₂

theorem programs : PolicyFiniteTargets.Programs := by
  intro p hp
  refine ⟨accepts_program p hp,admitted_program p hp,decision_program p hp,?_⟩
  unfold PolicyFinite.solve
  exact Computable.option_getD (decision_program p hp) (Computable.const false)
end LogicLineages.StandardControlCurrent.PolicyFiniteProof
