module
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphRowsTargets
import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsPrimitiveProof
import LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRowsPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
open HeterogeneousSignedMatrixSlice (RawRow)
open OriginalPrintedCircuitNumericRead (RawGate)
open OriginalPrintedRawGraphAllocator (OriginalArgs initialCode)
open OriginalPrintedRawBaseGateRows (StepArgs)

private theorem onGatePrimitive : Primrec onGate := by
  have tag : Primrec (fun p : StepArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have isBase : PrimrecPred (fun p : StepArgs => p.2.1 ≤ 1) :=
    Primrec.nat_le.comp tag (Primrec.const 1)
  exact Primrec.ite isBase OriginalPrintedRawBaseGateRows.exactOriginalRawBaseGateEffectivity.2.2.2
    OriginalPrintedRawFieldGateRows.exactOriginalRawFieldGateEffectivity.2

private theorem appendPrimitive : Primrec₂ appendEmission := by
  let A := List RawRow × State
  have n : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have out : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have all : Primrec (fun p : A => appendEmission p.1 p.2) :=
    n.pair (Primrec.list_append.comp Primrec.fst out)
  exact all.to₂

private theorem advancePresentPrimitive : Primrec₂ advancePresent := by
  let A := State × RawGate
  have n : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have prior : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have tape : Primrec (fun p : A => p.2) := Primrec.snd
  have h : Primrec (fun p : A => onGate (p.1.1,p.2)) := onGatePrimitive.comp (n.pair tape)
  have k : Primrec₂ (fun (p : A) (out : State) => appendEmission p.1.2 out) :=
    (appendPrimitive.comp (prior.comp Primrec.fst) Primrec.snd).to₂
  have both : Primrec (fun p : A => advancePresent p.1 p.2) := Primrec.option_map h k
  exact both.to₂

private theorem advancePrimitive : Primrec₂ advance := by
  let A := Option State × RawGate
  have k : Primrec₂ (fun (p : A) (s : State) => advancePresent s p.2) :=
    (advancePresentPrimitive.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have h : Primrec (fun p : A => advance p.1 p.2) := Primrec.option_bind Primrec.fst k
  exact h.to₂

private theorem runPrimitive : Primrec₂ run := by
  have k : Primrec₂ (fun (_ : FoldArgs) (s : Option State × RawGate) => advance s.1 s.2) :=
    (advancePrimitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  have t : Primrec (fun p : FoldArgs => run p.1 p.2) :=
    Primrec.list_foldl Primrec.fst Primrec.snd k
  exact t.to₂

private theorem rowsPrimitive (hi : Primrec initialCode) : Primrec rowsCode := by
  have t : Primrec (fun p : OriginalArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  have initial : Primrec (fun p : OriginalArgs => (some (initialCode p,[]) : Option State)) :=
    Primrec.option_some.comp (hi.pair (Primrec.const []))
  have after : Primrec (fun p : OriginalArgs => run p.2.2 (some (initialCode p,[]))) :=
    runPrimitive.comp t initial
  have drop : Primrec (Prod.snd : State → List RawRow) := Primrec.snd
  exact (Primrec.option_map₁ drop).comp after

theorem exactOriginalRawGraphRowsEffectivity : ExactOriginalRawGraphRowsEffectivity :=
  ⟨onGatePrimitive,advancePrimitive,runPrimitive,rowsPrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
