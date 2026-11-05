module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceRecursionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource
attribute [local irreducible] Nat.sqrt Nat.unpair SourceBooleanPrograms.Code.test

theorem admissible_primitive : Primrec Code.admissible :=
  Primrec.or.comp (SourceBooleanProgramsProof.test_primitive.comp (Primrec.snd.comp peelExists_primitive))
    (SourceBooleanProgramsProof.test_primitive.comp (Primrec.snd.comp peelForall_primitive))

theorem decide_primitive : Primrec₂ Code.decide := by
  let A := List Nat × Nat
  have he := peelExists_primitive.comp (Primrec.snd : Primrec (fun p : A => p.2))
  have ha := peelForall_primitive.comp (Primrec.snd : Primrec (fun p : A => p.2))
  have hp : PrimrecPred (fun p : A => SourceBooleanPrograms.Code.test (Code.peelExists p.2).2 = true) :=
    Primrec.eq.comp (SourceBooleanProgramsProof.test_primitive.comp (Primrec.snd.comp he)) (Primrec.const true)
  have hyes := SourceParameterDecisionProof.decideExists_primitive.comp
    ((Primrec.fst.comp he).pair (Primrec.fst.pair (Primrec.snd.comp he)))
  have hno := SourceParameterDecisionProof.decideForall_primitive.comp
    ((Primrec.fst.comp ha).pair (Primrec.fst.pair (Primrec.snd.comp ha)))
  exact Primrec.ite hp hyes hno

theorem actualNumericPrograms : HomogeneousSourceTargets.ActualNumericPrograms :=
  ⟨peelExists_primitive, peelForall_primitive, admissible_primitive, decide_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
