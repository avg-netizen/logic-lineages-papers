module
public import LogicLineages.PermittedControl.ActualBitFamilyRawRankTargets
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawRank
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open HeterogeneousSignedMatrixSlice (RawRow)
open ActualFiniteOrderBranches (Entry Pattern rename look)
open ActualBitFamilyRawLayout (RawBitRow RawFamily)

theorem rankPrimitive : Primrec rankCode := by
  let A := Pattern × Nat
  let P := A × (Entry × Nat)
  have es : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have key : Primrec (fun p : P => p.1.2) := Primrec.snd.comp Primrec.fst
  have entry : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have nm : Primrec (fun p : P => p.2.1.1) := Primrec.fst.comp entry
  have value : Primrec (fun p : P => p.2.1.2) := Primrec.snd.comp entry
  have acc : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : P => if p.2.1.1 = p.1.2 then p.2.1.2 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp nm key) value acc
  apply (Primrec.list_foldr es (Primrec.const 0) step.to₂).of_eq
  rintro ⟨⟨w,entries⟩,k⟩
  change entries.foldr (fun e t => if e.1 = k then e.2 else t) 0 = look Prod.fst Prod.snd k entries
  induction entries with
  | nil => rfl
  | cons first rest ih => simp only [List.foldr_cons,look,ih]

private theorem operandPrimitive : Primrec₂ operandCode := by
  let A := Pattern × LowerOperandCode
  have pattern : Primrec (fun p : A => p.1) := Primrec.fst
  have raw : Primrec (fun p : A => p.2) := Primrec.snd
  have tag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp raw
  have source : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp raw)
  have payload : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp raw)
  have rank := rankPrimitive.comp (pattern.pair source)
  have out : Primrec (fun p : A => operandCode p.1 p.2) := tag.pair (rank.pair payload)
  exact out.to₂

private theorem termPrimitive : Primrec₂ termCode := by
  let A := Pattern × WeightedCode
  have wt : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have op : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have out : Primrec (fun p : A => termCode p.1 p.2) := wt.pair (operandPrimitive.comp Primrec.fst op)
  exact out.to₂

private theorem rowPrimitive : Primrec₂ rowCode := by
  let A := Pattern × RawRow
  let T := A × WeightedCode
  have test : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have c : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have terms : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have pattern : Primrec (fun p : T => p.1.1) := Primrec.fst.comp Primrec.fst
  have op : Primrec (fun p : T => p.2) := Primrec.snd
  have mapped := Primrec.list_map terms (termPrimitive.comp pattern op).to₂
  have out : Primrec (fun p : A => rowCode p.1 p.2) := test.pair (c.pair mapped)
  exact out.to₂

private theorem bitPrimitive : Primrec₂ bitCode := by
  let A := Pattern × RawBitRow
  have row : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have bit : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have out : Primrec (fun p : A => bitCode p.1 p.2) :=
    (rowPrimitive.comp Primrec.fst row).pair bit
  exact out.to₂

theorem familyPrimitive : Primrec familyCode := by
  let A := Pattern × List RawBitRow
  let R := A × RawBitRow
  have pattern : Primrec (fun p : R => p.1.1) := Primrec.fst.comp Primrec.fst
  have row : Primrec (fun p : R => p.2) := Primrec.snd
  have clause : Primrec (fun p : A => p.2.map (bitCode p.1)) :=
    Primrec.list_map Primrec.snd (bitPrimitive.comp pattern row).to₂
  let F := Pattern × RawFamily
  let C := F × List RawBitRow
  have atPattern : Primrec (fun p : C => p.1.1) := Primrec.fst.comp Primrec.fst
  have one : Primrec (fun p : C => p.2) := Primrec.snd
  have mapClause : Primrec (fun p : C => p.2.map (bitCode p.1.1)) :=
    clause.comp (atPattern.pair one)
  exact Primrec.list_map (Primrec.snd : Primrec (Prod.snd : F → RawFamily)) mapClause.to₂

theorem exactRawRankEffectivity : ExactRawRankEffectivity := ⟨rankPrimitive,familyPrimitive⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawRank
