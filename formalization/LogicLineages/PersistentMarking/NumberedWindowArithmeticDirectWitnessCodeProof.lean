import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCodeTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawHopCodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectWitnessCodeProof
open NumberedWindowArithmeticDirectMultisetBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticFieldsProof
open NumberedWindowArithmeticNodeProof NumberedWindowArithmeticRawHopCodeProof
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticWitnessListCodeProof
open NumberedWindowArithmeticDirectCode

private theorem assembleInsertionRead (tag : Nat) (fs : List Nat) (e : InsertedOccurrence)
    (h : assembleInsertion tag fs = some e) : encodeInsertion e = encodeNode tag fs := by
  unfold assembleInsertion at h
  split at h
  · cases h; rfl
  · cases h

theorem insertionRead (n : Nat) (e : InsertedOccurrence) (h : decodeInsertion n = some e) :
    encodeInsertion e = n :=
  taggedSound encodeInsertion assembleInsertion assembleInsertionRead n e h

theorem insertionRound (e : InsertedOccurrence) : decodeInsertion (encodeInsertion e) = some e := by
  cases e
  simp [decodeInsertion,encodeInsertion,nodeRound,assembleInsertion]

private theorem assembleWitnessRead (tag : Nat) (fs : List Nat) (w : DirectMultisetWitness)
    (h : assembleDirectWitness tag fs = some w) : encodeDirectWitness w = encodeNode tag fs := by
  unfold assembleDirectWitness at h
  split at h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨kept,hk,removed,hr,es,he,rfl⟩ := h
    have hList := decodeSound encodeInsertion decodeInsertion insertionRead _ _ he
    simp only [encodeDirectWitness,fieldsRead hk,fieldsRead hr,hList]
  · cases h

theorem witnessRead (n : Nat) (w : DirectMultisetWitness) (h : decodeDirectWitness n = some w) :
    encodeDirectWitness w = n :=
  taggedSound encodeDirectWitness assembleDirectWitness assembleWitnessRead n w h

theorem witnessRound (w : DirectMultisetWitness) :
    decodeDirectWitness (encodeDirectWitness w) = some w := by
  cases w
  simp [decodeDirectWitness,encodeDirectWitness,nodeRound,assembleDirectWitness,fieldsRound,
    decodeRound encodeInsertion decodeInsertion insertionRound]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectWitnessCodeProof
