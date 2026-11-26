module
public import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyTargets
import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalMachinePrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
open HeterogeneousSignedMatrixSlice (RawRow)
open ActualBitFamilyRawLayout (RawBitRow)
open OriginalPrintedTerminalBitClauses (vectors)
open OriginalPrintedRawPositionalTerminal (finishCode exactOriginalRawPositionalEffectivity)
open OrdinalComparison.LayeredComparison.CommonHeadCode.Program (zipWith_primitive)

private theorem vectorsPrimitive : Primrec vectors := by
  let L := List (List Bool)
  have prep (b : Bool) : Primrec (fun xs : L => xs.map (List.cons b)) :=
    Primrec.list_map Primrec.id (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂
  have grow : Primrec (fun xs : L => xs.map (List.cons false) ++ xs.map (List.cons true)) :=
    Primrec.list_append.comp (prep false) (prep true)
  have step : Primrec₂ (fun (_ : Nat) (xs : L) => xs.map (List.cons false) ++ xs.map (List.cons true)) :=
    (grow.comp (Primrec.snd : Primrec (Prod.snd : Nat × L → L))).to₂
  apply (Primrec.nat_rec₁ ([[]] : L) step).of_eq
  intro n
  induction n <;> simp_all [vectors]

private theorem acceptedPrimitive : Primrec acceptedCode := by
  let P := List Bool × ChoiceArgs
  have key : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have rawBits : Primrec (Prod.fst : P → List Bool) := Primrec.fst
  have yes : Primrec (fun p : P => some p.2.2.1) :=
    Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have value : Primrec (fun p : P => finishCode (p.2.1,p.1)) :=
    exactOriginalRawPositionalEffectivity.2.2.comp (key.pair rawBits)
  have accept : PrimrecRel (fun (bits : List Bool) (p : ChoiceArgs) =>
      finishCode (p.1,bits) = some p.2.1) := Primrec.eq.comp value yes
  have size : Primrec (fun p : ChoiceArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  exact accept.listFilter.comp (vectorsPrimitive.comp size) Primrec.id

private theorem prefixPrimitive : Primrec (fun rows : List RawRow => rows.map (fun row => (row,true))) := by
  have item : Primrec (fun t : List RawRow × RawRow => (t.2,true)) :=
    Primrec.snd.pair (Primrec.const true)
  exact Primrec.list_map Primrec.id item.to₂

private theorem suffixPrimitive : Primrec₂ (List.zip : List RawRow → List Bool → List RawBitRow) :=
  zipWith_primitive Prod.mk Primrec₂.pair

private theorem bodyPrimitive : Primrec (fun p : (List RawRow × List RawRow) × List Bool =>
    p.1.1.map (fun row => (row,true)) ++ p.1.2.zip p.2) := by
  let P := (List RawRow × List RawRow) × List Bool
  have pre : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have tail : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.list_append.comp (prefixPrimitive.comp pre) (suffixPrimitive.comp tail Primrec.snd)

private theorem clausesPrimitive : Primrec clausesCode := by
  have code : Primrec (fun p : Args => p.1) := Primrec.fst
  have polarity : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp Primrec.snd
  have tapes : Primrec (fun p : Args => p.2.2) := Primrec.snd.comp Primrec.snd
  have n : Primrec (fun p : Args => p.2.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp tapes)
  have choices : Primrec (fun p : Args => acceptedCode (p.1,p.2.1,p.2.2.2.length)) :=
    acceptedPrimitive.comp (code.pair (polarity.pair n))
  have item : Primrec (fun p : Args × List Bool =>
      p.1.2.2.1.map (fun row => (row,true)) ++ p.1.2.2.2.zip p.2) :=
    bodyPrimitive.comp ((tapes.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.list_map choices item.to₂

theorem exactOriginalRawClauseEffectivity : ExactOriginalRawClauseEffectivity :=
  ⟨vectorsPrimitive,acceptedPrimitive,clausesPrimitive⟩

end LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
