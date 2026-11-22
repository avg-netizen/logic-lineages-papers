module
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocatorTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDataProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (RawGate)

private theorem outputPrimitive : Primrec outputCode :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem referencesPrimitive : Primrec referencesCode := by
  have tag : Primrec (Prod.fst : RawGate → Nat) := Primrec.fst
  have source : Primrec (fun g : RawGate => g.2.1) := Primrec.fst.comp Primrec.snd
  have expr : Primrec (fun g : RawGate => g.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have args : Primrec (fun g : RawGate => g.2.2.2.2.2) := Primrec.snd.comp expr
  have item : Primrec (fun p : RawGate × (Int × Nat) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0))
    (Primrec.list_map args item.to₂)
    (Primrec.list_cons.comp source (Primrec.const []))

private theorem namesPrimitive : Primrec namesCode :=
  Primrec.list_append.comp (Primrec.list_map Primrec.id (outputPrimitive.comp Primrec.snd).to₂)
    (Primrec.list_flatMap Primrec.id (referencesPrimitive.comp Primrec.snd).to₂)

private theorem basesPrimitive : Primrec baseCodes := by
  have keep : PrimrecPred (fun g : RawGate => g.1 ≤ 1) :=
    Primrec.nat_le.comp Primrec.fst (Primrec.const 1)
  exact Primrec.listFilter keep

private theorem maxFold : Primrec (fun p : List Nat × Nat => p.1.foldr max p.2) := by
  let A := List Nat × Nat
  let B := Nat × Nat
  have pull : Primrec (fun p : A × B => max p.2.1 p.2.2) :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst Primrec.snd pull.to₂

private theorem exteriorPrimitive : Primrec exteriorCode := by
  have vars : Primrec (fun p : ExteriorArgs => MaximalPlainBranchPrograms.Code.variables p.2) :=
    MaximalPlainBranchProgramsProof.variables_primitive.comp Primrec.snd
  exact maxFold.comp (Primrec.fst.pair (maxFold.comp (vars.pair (Primrec.const 0))))

private theorem protectedPrimitive : Primrec protectedCode :=
  maxFold.comp ((namesPrimitive.comp Primrec.snd).pair Primrec.fst)

private theorem firstPrimitive : Primrec firstHiddenCode :=
  Primrec.succ.comp (protectedPrimitive.comp (protectedPrimitive.pair (basesPrimitive.comp Primrec.snd)))

private theorem initialPrimitive : Primrec initialCode := by
  let A := OriginalArgs
  have known : Primrec (fun p : A => p.1) := Primrec.fst
  have pcode : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have tape : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  exact firstPrimitive.comp ((exteriorPrimitive.comp (known.pair pcode)).pair tape)

theorem exactOriginalRawGraphAllocatorEffectivity : ExactOriginalRawGraphAllocatorEffectivity :=
  ⟨namesPrimitive,basesPrimitive,exteriorPrimitive,initialPrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocator
