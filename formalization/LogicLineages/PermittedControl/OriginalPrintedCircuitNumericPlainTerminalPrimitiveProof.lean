module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminalTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProgramsDataProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeRecursionProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProgramsProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProgramsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitNumericRead (bank)

theorem allPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {ls : A → List B} {pred : A → B → Bool} (hl : Primrec ls) (hp : Primrec₂ pred) :
    Primrec (fun x => (ls x).all (pred x)) := by
  let P := A × (B × Bool)
  have hstep : Primrec (fun p : P => pred p.1 p.2.1 && p.2.2) :=
    Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hl (Primrec.const true) hstep.to₂).of_eq
  intro x
  generalize ls x = xs
  induction xs with
  | nil => rfl
  | cons a as ih => simp [List.foldr_cons,List.all_cons,ih]

theorem namesFitPrimitive : Primrec namesFit := by
  let A := List Nat × List Nat
  let P := A × Nat
  have len : Primrec (fun p : P => p.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have check : Primrec (fun p : P => decide (p.2 < p.1.1.length)) :=
    (Primrec.nat_lt.comp Primrec.snd len).decide
  exact allPrimitive (Primrec.snd : Primrec (Prod.snd : A → List Nat)) check.to₂

private theorem atomVariablesOnlyPrimitive : Primrec atomVariablesOnly := by
  let Term := Int × NormalForm.Code.ItemData
  let P := Nat × Term
  let Arg := NormalForm.Code.AtomData
  have row : Primrec (fun a : Arg => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have terms := row.comp LinearRowsCodeProof.decodeAtom_primitive
  have tag : Primrec (fun p : P => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have check : Primrec (fun p : P => decide (p.2.2.1 = 0)) :=
    (Primrec.eq.comp tag (Primrec.const 0)).decide
  exact allPrimitive terms check.to₂

private theorem variablesOnlyPrimitive : Primrec variablesOnly := by
  let P := Nat × Nat
  have each : Primrec (fun p : P => atomVariablesOnly p.2) := atomVariablesOnlyPrimitive.comp Primrec.snd
  exact allPrimitive LinearRowsCodeProof.atoms_primitive each.to₂

theorem plainGuardPrimitive : Primrec plainGuard :=
  Primrec.and.comp (variablesOnlyPrimitive.comp Primrec.snd)
    (namesFitPrimitive.comp (Primrec.fst.pair
      (MaximalPlainBranchProgramsProof.variables_primitive.comp Primrec.snd)))

theorem plainAnswerPrimitive : Primrec plainAnswer := by
  let P := TestArgs × (Nat × Nat)
  have names : Primrec (fun p : TestArgs => MaximalPlainBranchPrograms.Code.variables p.2) :=
    MaximalPlainBranchProgramsProof.variables_primitive.comp Primrec.snd
  have name : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have values : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have value : Primrec (fun p : P => bank p.1.1 p.2.1) := (Primrec.list_getD 0).comp values name
  have residual : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : P => BoundedRows.Code.formula p.2.1 (bank p.1.1 p.2.1) p.2.2) :=
    BoundedRowsCodeProof.formula_primitive.comp (name.pair value) residual
  exact ZeroValuationProof.actualNumericPrograms.2.2.2.comp
    (Primrec.list_foldr names Primrec.snd step.to₂)

theorem boolCodePrimitive : Primrec boolCode := by
  exact (Primrec.cond Primrec.id (Primrec.const 5) (Primrec.const 4)).of_eq (fun b => by cases b <;> rfl)

theorem finishPlainPrimitive : Primrec finishPlain :=
  (Primrec.cond plainGuardPrimitive (boolCodePrimitive.comp plainAnswerPrimitive)
    (Primrec.const 0)).of_eq (fun p => by cases h : plainGuard p <;> simp [finishPlain,h])

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericPlainTerminal
