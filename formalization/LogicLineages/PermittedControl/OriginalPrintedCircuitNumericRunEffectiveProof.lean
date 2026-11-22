module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRunTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadEffectiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
open OrdinalComparison
open OriginalPrintedCircuitNumericRead (RawGate readComputable)

private theorem installPrimitive : Primrec install := by
  let P := List Nat × Nat × Nat
  have bank : Primrec (Prod.fst : P → List Nat) := Primrec.fst
  have dst : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have code : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have value := Primrec.nat_sub.comp code (Primrec.const 4)
  have changed := Primrec.list_set.comp bank (dst.pair value)
  exact Primrec.ite (Primrec.nat_lt.comp code (Primrec.const 4))
    (Primrec.sumInl.comp code) (Primrec.sumInr.comp changed)

private theorem stepComputable (f : Nat → Nat) (hf : Computable f) : Computable (step f) := by
  have vals : Primrec (Prod.fst : StepArgs → List Nat) := Primrec.fst
  have out : Primrec (fun p : StepArgs => rawOutput p.2) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have cap := (Primrec.nat_lt.comp out (Primrec.list_length.comp vals)).decide
  have data := vals.to_comp.pair (out.to_comp.pair (readComputable f hf))
  apply (Computable.cond cap.to_comp (installPrimitive.to_comp.comp data)
    (Computable.const (Sum.inl 0 : State))).of_eq
  intro p
  by_cases h : rawOutput p.2 < p.1.length <;> simp [step,h]

private theorem carryComputable (f : Nat → Nat) (hf : Computable f) : Computable (stepCarry f) := by
  let P := State × RawGate
  let Rejected := P × Nat
  let Good := P × List Nat
  have choose : Computable (Prod.fst : P → State) := Computable.fst
  have err : Computable (fun p : Rejected => (Sum.inl p.2 : State)) :=
    (Primrec.sumInl.comp Primrec.snd).to_comp
  have more : Computable (fun p : Good => step f (p.2,p.1.2)) :=
    (stepComputable f hf).comp
      (Computable.snd.pair (Computable.snd.comp Computable.fst))
  exact (Computable.sumCasesOn choose err.to₂ more.to₂).of_eq (fun p => by
    rcases p with ⟨state,g⟩
    cases state <;> rfl)

theorem runCodeComputable (f : Nat → Nat) (hf : Computable f) : Computable (runCode f) := by
  let P := Args × (State × RawGate)
  have next : Computable₂ (fun (_ : Args) (p : State × RawGate) => stepCarry f p) :=
    ((carryComputable f hf).comp
      (Computable.snd : Computable (Prod.snd : P → State × RawGate))).to₂
  have init : Computable (fun p : Args => (Sum.inr p.1 : State)) :=
    (Primrec.sumInr.comp Primrec.fst).to_comp
  exact LayeredComparison.BalancedBoxEvaluation.Graph.computable_foldl
    ((0,0,0,(0,0),(0,[])) : RawGate) Computable.snd init next

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRun
