module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserUnpackProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseFieldCell (chosenCell cellGood cellHead cellTail)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (decodeResult)
open NumberedWindowInternalSparseFieldParserRawPairProof (decodedPair encodedPair)
open NumberedWindowInternalSparseFieldParserUnpackProof (casesUnpack)
open NumberedWindowInternalSparseFieldParserNumericChecks (exact_ActualDecodedOutput)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (pack unpack unpackNode)

theorem cellAt (h t : Nat) : chosenCell (pair h t + 1) = some (h,t) :=
  (allInput.2 (pair h t)).trans (encodedPair h t)

theorem codeOfCell {n h t : Nat} (found : chosenCell n = some (h,t)) :
    n = pair h t + 1 := by
  cases n with
  | zero => rw [allInput.1] at found; cases found
  | succ n =>
    have hit := (allInput.2 n).symm.trans found
    rw [decodedPair hit]

theorem flagOfCell {n h t : Nat} (found : chosenCell n = some (h,t)) :
    run cellGood n = 1 := by
  by_cases flag : run cellGood n = 1
  · exact flag
  · change evaluate cellGood (n ::ᵥ nil) ≠ 1 at flag
    simp only [chosenCell,if_neg flag] at found
    cases found

theorem headTailOfCell {n h t : Nat} (found : chosenCell n = some (h,t)) :
    run cellHead n = h ∧ run cellTail n = t := by
  have flag := flagOfCell found
  change evaluate cellGood (n ::ᵥ nil) = 1 at flag
  have eq : (run cellHead n,run cellTail n) = (h,t) := by
    apply Option.some.inj
    simpa only [chosenCell,run,if_pos flag] using found
  exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩

theorem noFlagOfNone {n : Nat} (missing : chosenCell n = none) :
    run cellGood n ≠ 1 := by
  intro flag
  change evaluate cellGood (n ::ᵥ nil) = 1 at flag
  simp only [chosenCell,if_pos flag] at missing
  cases missing

theorem emptyUnpack : unpack 0 = some [] := casesUnpack.1

theorem missingUnpack {n : Nat} (nonzero : n ≠ 0) (missing : chosenCell n = none) :
    unpack n = none := by
  cases n with
  | zero => exact False.elim (nonzero rfl)
  | succ n => exact casesUnpack.2.1 n missing

theorem splitUnpack {n h t : Nat} (found : chosenCell n = some (h,t)) :
    unpack n = (unpack t).map (fun xs => h :: xs) := by
  rw [codeOfCell found]
  exact casesUnpack.2.2 h t

theorem packOfUnpack {xs : List Nat} (n : Nat) (unpacked : unpack n = some xs) :
    n = pack xs := by
  induction xs generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n =>
      cases found : chosenCell (n+1) with
      | none => rw [missingUnpack (Nat.succ_ne_zero n) found] at unpacked; cases unpacked
      | some pair =>
        obtain ⟨h,t⟩ := pair
        rw [splitUnpack found] at unpacked
        cases tail : unpack t <;> rw [tail] at unpacked <;> cases unpacked
  | cons x xs ih =>
    cases n with
    | zero => rw [emptyUnpack] at unpacked; cases unpacked
    | succ n =>
      cases found : chosenCell (n+1) with
      | none => rw [missingUnpack (Nat.succ_ne_zero n) found] at unpacked; cases unpacked
      | some pair =>
        obtain ⟨h,t⟩ := pair
        rw [splitUnpack found] at unpacked
        cases tail : unpack t with
        | none => rw [tail] at unpacked; cases unpacked
        | some ys =>
          rw [tail] at unpacked
          have joined : h::ys = x::xs := Option.some.inj unpacked
          have same := List.cons.inj joined
          rw [codeOfCell found,pack,same.1,ih t (tail.trans (congrArg some same.2))]

theorem node : AllInputTaggedNode := by
  intro n
  cases n with
  | zero => rw [selectedNode, allInput.1] <;> rfl
  | succ n =>
    rw [selectedNode,allInput.2 n,unpackNode]
    cases decoded : decode n with
    | none => simp only [decoded,Option.bind_eq_bind,Option.bind_none]
    | some pair =>
      obtain ⟨tag,body⟩ := pair
      simp only [decoded,Option.bind_eq_bind,Option.bind_some,run,exact_ActualDecodedOutput]

theorem nodeOfCell {n h t : Nat} (found : chosenCell n = some (h,t)) :
    unpackNode n = (unpack t).map (fun xs => (h,xs)) := by
  rw [← node n, selectedNode, found]
  simp only [Option.bind_eq_bind,Option.bind_some,run,exact_ActualDecodedOutput]
  cases unpack t <;> rfl

theorem noNode {n : Nat} (found : chosenCell n = none) : unpackNode n = none := by
  rw [← node n, selectedNode, found] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
