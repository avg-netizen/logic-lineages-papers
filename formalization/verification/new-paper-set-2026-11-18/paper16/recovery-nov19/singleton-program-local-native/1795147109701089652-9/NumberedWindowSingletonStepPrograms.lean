module
public import LogicLineages.PersistentMarking.NumberedWindowSingletonProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowShiftProgramProof
import LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowSingletonStepPrograms
open NumberedWindowSingletonAlgorithm
open NumberedWindowShiftAlgorithm (Table Row)
open NumberedWindowShiftStepPrograms (Env Node StepInput argsNextPrim)
open NumberedWindowMarkRootProgramProof (nodePrim readPrim)

theorem partsPrim : Primrec (fun p : Env × Node =>
    termParts p.1.2.2.2 p.1.1 p.1.2.1 p.1.2.2.1 p.2.1 p.2.2) := by
  let P := Env × Node
  have fs : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have tag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have arg : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have depth : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have offset : Primrec (fun p : P => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have data : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have inherited := NumberedWindowShiftStepPrograms.termPartsPrim.comp
    (((Primrec.const 0).pair data).pair Primrec.snd)
  let value (i : Nat) := (Primrec.list_getD 0).comp fs (Primrec.const i)
  have current := Primrec.nat_add.comp depth offset
  have lifted := NumberedWindowShiftProgramProof.outputPrim.comp
    (current.pair ((Primrec.const 0).pair arg))
  have hit := Primrec.option_getD.comp (Primrec.fst.comp lifted) (Primrec.const 0)
  have outer := nodePrim.comp (Primrec.const 1) (Primrec.list_cons.comp (value 0)
    (Primrec.list_cons.comp (Primrec.pred.comp (value 1)) (Primrec.const [])))
  have boundCase := Primrec.ite (Primrec.nat_lt.comp (value 1) current) (nodePrim.comp (Primrec.const 1) fs)
    (Primrec.ite (Primrec.eq.comp (value 1) current) hit outer)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) boundCase inherited

theorem nextPrim : Primrec (fun p : StepInput => next p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let E := StepInput × Node
  have arg : Primrec (fun p : E => p.1.1) := Primrec.fst.comp Primrec.fst
  have depth : Primrec (fun p : E => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have offset : Primrec (fun p : E => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have tab : Primrec (fun p : E => p.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have env := arg.pair (depth.pair (offset.pair tab))
  have code : Primrec (fun p : StepInput => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tm := Primrec.option_getD.comp (Primrec.option_map (readPrim.comp code)
    (partsPrim.comp (env.pair Primrec.snd)).to₂) (Primrec.const 0)
  exact tm.pair (argsNextPrim.comp (Primrec.snd.comp Primrec.snd : Primrec (fun p : StepInput => p.2.2)))
end LogicLineages.PersistentMarking.NumberedWindowSingletonStepPrograms
