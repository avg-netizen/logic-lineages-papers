module
public import LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecializationTargets

public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecialization
open Nat.Partrec (Code)

theorem jointProgramIndexSpecialization : JointProgramIndexSpecialization := by
  intro joint hj
  obtain ⟨c, hc⟩ := Code.exists_code.mp hj
  refine ⟨fun e => c.curry (Encodable.encode e), ?_, ?_⟩
  · exact Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode
  · intro e x
    rw [Code.eval_curry, hc]

theorem jointAnswerIndexSpecialization : JointAnswerIndexSpecialization := by
  intro joint admitted answer hj ha
  obtain ⟨compile, hpr, hEval⟩ := jointProgramIndexSpecialization joint hj
  refine ⟨compile, hpr, fun e x hx => ?_⟩
  rw [hEval, ha e x hx]

#print axioms jointProgramIndexSpecialization
#print axioms jointAnswerIndexSpecialization
end LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecialization
