module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminalNamesProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunEffectiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTypedProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsCalibrationProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsAnswerProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (bank encodeGate)
open OriginalPrintedCircuitNumericRun (runCode EncodesRun exactNumericTypedRun runCodeComputable)
open OriginalPrintedCircuitNumericPlainTerminal
  (TestArgs Args namesFit boolCode packTerminal namesFitPrimitive boolCodePrimitive)
open OriginalPrintedCircuitSequential (run)
open OriginalPrintedCircuitTerminal (observe)
open OriginalMixedTerminalTest (Test boundedNames)

private theorem finishComputable : Computable finishBounded := by
  have admissionCheck : Computable (fun p : TestArgs => BoundedSourcePrograms.Code.test p.2) :=
    BoundedSourceProgramsProof.test_computable.comp Computable.snd
  have availability : Computable (fun p : TestArgs => namesFit (p.1,namesCode p.2)) :=
    namesFitPrimitive.to_comp.comp (Computable.fst.pair (namesComputable.comp Computable.snd))
  have checked : Computable boundedGuard := Primrec.and.to_comp.comp admissionCheck availability
  have present : Computable (fun p : TestArgs => boolCode (BoundedSourcePrograms.Code.answer p.1 p.2)) :=
    boolCodePrimitive.to_comp.comp BoundedSourceProgramsProof.answer_computable
  exact (Computable.cond checked present (Computable.const 0)).of_eq
    (fun p => by cases h : boundedGuard p <;> simp [finishBounded,h])

theorem exactBoundedTerminalData : ExactBoundedTerminalData := by
  refine ⟨namesComputable,finishComputable,namesCalibrate,?_,?_⟩
  · intro values p
    simp only [boundedGuard,Bool.and_eq_true_iff,namesFit,List.all_eq_true,decide_eq_true_eq,
      namesCalibrate,Test.Admitted]
    rw [BoundedSourceProgramsProof.literalSyntaxCode p]
  · intro values p
    exact BoundedSourceProgramsProof.literalAnswerCode values p

private theorem observeComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (observeBoundedCode f) := by
  let Bad := Args × Nat
  let Good := Args × List Nat
  have result : Computable (fun p : Args => runCode f p.1) :=
    (runCodeComputable f hf).comp Computable.fst
  have stop : Computable (Prod.snd : Bad → Nat) := Computable.snd
  have finish : Computable (fun p : Good => finishBounded (p.2,p.1.2)) :=
    finishComputable.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact (Computable.sumCasesOn result stop.to₂ finish.to₂).of_eq (fun p => by
    cases hx : runCode f p.1 <;> simp [observeBoundedCode,hx])

theorem exactNumericBoundedTerminalRun : ExactNumericBoundedTerminalRun := by
  refine ⟨observeComputable,?_,?_⟩
  · intro f p why stop
    simp only [observeBoundedCode,stop]
  · intro f known gates top values p fit admitted inputs
    have aligned := exactNumericTypedRun f known gates top values fit
    cases raw : runCode f (values,gates.map encodeGate) with
    | inl why =>
        cases actual : run f (bank values) gates with
        | error cause =>
            have first := aligned
            rw [raw,actual,EncodesRun] at first
            simp only [observeBoundedCode,raw,observe,actual,packTerminal]
            exact first
        | ok final => simp [raw,actual,EncodesRun] at aligned
    | inr bank' =>
        cases actual : run f (bank values) gates with
        | error cause => simp [raw,actual,EncodesRun] at aligned
        | ok final =>
            have both := aligned
            rw [raw,actual,EncodesRun] at both
            obtain ⟨size,valuesExact⟩ := both
            have reach : ∀ n ∈ boundedNames p, n < bank'.length := by
              rw [size]
              exact inputs
            have guard := (exactBoundedTerminalData.2.2.2.1 bank' p).mpr ⟨admitted,reach⟩
            have answer := exactBoundedTerminalData.2.2.2.2 bank' p
            simp only [observeBoundedCode,raw,finishBounded,guard,if_true,observe,actual,packTerminal]
            rw [answer,valuesExact]

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminal
