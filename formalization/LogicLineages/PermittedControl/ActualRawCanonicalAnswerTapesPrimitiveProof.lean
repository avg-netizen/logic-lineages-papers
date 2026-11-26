module
public import LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapesTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataPrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
open ActualCanonicalOperandGrouping (RawTerm)
open ActualRawCanonicalNodeMetadata (labelsCode labelsPrimitive)

private def nextTapes (old : List (List Nat)) : List (List Nat) :=
  [0,1,2].flatMap (fun digit => old.map (List.cons digit))

private theorem nextTapesPrimitive : Primrec nextTapes := by
  let A := List (List Nat) × Nat
  let S := A × List Nat
  have old : Primrec (Prod.fst : A → List (List Nat)) := Primrec.fst
  have digit : Primrec (fun p : S => p.1.2) := Primrec.snd.comp Primrec.fst
  have tape : Primrec (Prod.snd : S → List Nat) := Primrec.snd
  have prependTape : Primrec (fun p : A => p.1.map (List.cons p.2)) :=
    Primrec.list_map old (Primrec.list_cons.comp digit tape).to₂
  exact Primrec.list_flatMap (Primrec.const [0,1,2]) prependTape.to₂

theorem answerTapesPrimitive : Primrec answerTapes := by
  apply (Primrec.nat_rec' Primrec.id (Primrec.const ([[]] : List (List Nat)))
    (nextTapesPrimitive.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp_all [answerTapes,nextTapes]

theorem pairWidthPrimitive : Primrec pairWidth := by
  have width : Primrec (fun ts : List RawTerm => (labelsCode ts).length) :=
    Primrec.list_length.comp labelsPrimitive
  exact Primrec.nat_mul.comp width width

theorem candidateTapesPrimitive : Primrec candidateTapes :=
  answerTapesPrimitive.comp pairWidthPrimitive

theorem exactRawAnswerTapeEffectivity : ExactRawAnswerTapeEffectivity :=
  ⟨answerTapesPrimitive,pairWidthPrimitive,candidateTapesPrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalAnswerTapes
