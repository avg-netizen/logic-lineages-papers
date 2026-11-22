module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalCalibrationProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunEffectiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTypedProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
open OriginalPrintedCircuitNumericRead (bank encodeGate packResult)
open OriginalPrintedCircuitNumericRun (runCode EncodesRun State exactNumericTypedRun runCodeComputable)
open OriginalPrintedCircuitSequential (run)
open OriginalPrintedCircuitTerminal (observe)

private theorem observeComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (observePlainCode f) := by
  let Bad := Args × Nat
  let Good := Args × List Nat
  have result : Computable (fun p : Args => runCode f p.1) :=
    (runCodeComputable f hf).comp Computable.fst
  have stop : Computable (Prod.snd : Bad → Nat) := Computable.snd
  have finish : Computable (fun p : Good => finishPlain (p.2,p.1.2)) :=
    finishPlainPrimitive.to_comp.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact (Computable.sumCasesOn result stop.to₂ finish.to₂).of_eq (fun p => by
    cases hx : runCode f p.1 <;> simp [observePlainCode,hx])

theorem exactNumericPlainTerminalRun : ExactNumericPlainTerminalRun := by
  refine ⟨observeComputable,?_,?_⟩
  · intro f p why stop
    simp only [observePlainCode,stop]
  · intro f known gates top values p fit admitted inputs
    have aligned := exactNumericTypedRun f known gates top values fit
    cases raw : runCode f (values,gates.map encodeGate) with
    | inl why =>
        cases actual : run f (bank values) gates with
        | error cause =>
            have first := aligned
            rw [raw,actual,EncodesRun] at first
            change observePlainCode f ((values,gates.map encodeGate),p.encode) = _
            simp only [observePlainCode,raw,observe,actual,packTerminal]
            exact first
        | ok final => simp [raw,actual,EncodesRun] at aligned
    | inr bank' =>
        cases actual : run f (bank values) gates with
        | error cause => simp [raw,actual,EncodesRun] at aligned
        | ok final =>
            have both := aligned
            rw [raw,actual,EncodesRun] at both
            obtain ⟨size,valuesExact⟩ := both
            have reach : ∀ n ∈ p.variables, n < bank'.length := by
              rw [size]
              exact inputs
            have guard := (exactPlainTerminalData.2.2.2.1 bank' p).mpr ⟨admitted,reach⟩
            have answer := exactPlainTerminalData.2.2.2.2 bank' p admitted
            simp only [observePlainCode,raw,finishPlain,guard,if_true,observe,actual,packTerminal]
            rw [answer,valuesExact]

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
