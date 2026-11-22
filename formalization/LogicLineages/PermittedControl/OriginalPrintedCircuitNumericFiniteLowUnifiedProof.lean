module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLowTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalRunProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericBoundedTerminalProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunEffectiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
open OriginalPrintedCircuitNumericPlainTerminal (finishPlainPrimitive exactNumericPlainTerminalRun)
open OriginalPrintedCircuitNumericBoundedTerminal (exactBoundedTerminalData exactNumericBoundedTerminalRun)
open OriginalPrintedCircuitNumericRun (runCode runCodeComputable)
open OriginalMixedTerminalTest (Test)

private theorem finishComputable : Computable finish := by
  let P := List Nat × RawTest
  have testTag : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have code : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have input : Primrec (fun p : P => (p.1,p.2.2)) := Primrec.fst.pair code
  have plain := finishPlainPrimitive.to_comp.comp input.to_comp
  have bounded := exactBoundedTerminalData.2.1.comp input.to_comp
  have isTag (n : Nat) := (Primrec.eq.comp testTag (Primrec.const n)).decide.to_comp
  apply (Computable.cond (isTag 0) plain
    (Computable.cond (isTag 1) bounded (Computable.const 0))).of_eq
  intro p
  by_cases h0 : p.2.1 = 0 <;> by_cases h1 : p.2.1 = 1 <;> simp [finish,h0,h1]

private theorem observeComputable (f : Nat → Nat) (hf : Computable f) :
    Computable (observeCode f) := by
  let Bad := EvalArgs × Nat
  let Good := EvalArgs × List Nat
  have params : Computable (fun p : EvalArgs => (p.1,p.2.1)) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have result := (runCodeComputable f hf).comp params
  have stop : Computable (Prod.snd : Bad → Nat) := Computable.snd
  have finishC : Computable (fun p : Good => finish (p.2,p.1.2.2)) :=
    finishComputable.comp (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact (Computable.sumCasesOn result stop.to₂ finishC.to₂).of_eq (fun p => by
    cases hx : runCode f (p.1,p.2.1) <;> simp [observeCode,hx])

theorem exactUnifiedNumericTerminal : ExactUnifiedNumericTerminal := by
  refine ⟨observeComputable,?_,?_⟩
  · intro f p why stop
    simp only [observeCode,stop]
  · intro f known gates top values p fits hp refs
    cases p with
    | rows q =>
        have calibrated := exactNumericPlainTerminalRun.2.2 f known gates top values q fits hp refs
        cases h : runCode f (values,gates.map OriginalPrintedCircuitNumericRead.encodeGate) <;>
          simpa [observeCode,OriginalPrintedCircuitNumericPlainTerminal.observePlainCode,
            encodeTest,finish,h] using calibrated
    | bounded q =>
        have calibrated := exactNumericBoundedTerminalRun.2.2 f known gates top values q fits hp refs
        cases h : runCode f (values,gates.map OriginalPrintedCircuitNumericRead.encodeGate) <;>
          simpa [observeCode,OriginalPrintedCircuitNumericBoundedTerminal.observeBoundedCode,
            encodeTest,finish,h] using calibrated

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericFiniteLow
