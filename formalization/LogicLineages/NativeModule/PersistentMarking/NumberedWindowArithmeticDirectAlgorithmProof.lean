module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmProof
open NumberedWindowArithmeticDirectAlgorithmTargets NumberedWindowDirectAlgorithm
open NumberedWindowArithmeticDirectCode NumberedWindowArithmeticDirectMultisetBits
open NumberedWindowArithmeticFields NumberedWindowFieldAlgorithm
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticFieldAlgorithmChecks

private theorem originalFields : unpack = decodeFields := exact_ExactOrderedFieldCodec.2.symm
private theorem originalNode : unpackNode = decodeNode := exact_ExactTaggedNodeCodec.2.symm

private theorem oneEntry (n : Nat) : readEntry n = (decodeInsertion n).map entry := by
  unfold readEntry decodeInsertion
  rw [originalNode]
  cases hn : decodeNode n with
  | none => rfl
  | some p =>
    rcases p with ⟨tag,xs⟩
    simp only [Option.bind_eq_bind, Option.bind_some]
    unfold assembleInsertion
    split <;> split <;> first | rfl | grind [entry]

private theorem allEntries (xs : List Nat) :
    entries xs = (decodeElements decodeInsertion xs).map (List.map entry) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [entries, oneEntry, decodeElements, ih]
    cases h : decodeInsertion x <;> cases hs : decodeElements decodeInsertion xs <;> rfl

private theorem oneWitness (n : Nat) : readWitness n = (decodeDirectWitness n).map witness := by
  unfold readWitness decodeDirectWitness
  rw [originalNode]
  cases hn : decodeNode n with
  | none => rfl
  | some p =>
    rcases p with ⟨tag,xs⟩
    fun_cases assembleDirectWitness tag xs
    case case1 k r a =>
      simp only [assembleDirectWitness, originalFields, decodeListOf]
      cases hk : decodeFields k <;> cases hr : decodeFields r <;> cases ha : decodeFields a <;> simp [hk,hr,ha,allEntries,witness]
      rename_i items
      cases hi : decodeElements decodeInsertion items <;> simp [hi, witness]
    case case2 bad =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      unfold assembleDirectWitness
      split <;> split <;> first | rfl | grind

theorem decoders : LiteralOccurrenceDecoders := ⟨oneEntry, oneWitness⟩

private theorem lists (S : Spine.Signature) (K : List Ty) (xs ys : List Nat) (w : DirectMultisetWitness) :
    directLists (NumberedWindowArithmeticAllContextBits.addressBit S K)
      (NumberedWindowArithmeticAllContextBits.addressRSBit S K) xs ys (witness w) =
      directMultisetBit S K xs ys w := by
  simp [directLists, directMultisetBit, typedAddressListBit, insertionBit, witness, entry,List.map_map,Function.comp_def]
  rfl

theorem checkers : OriginalMultisetCheckerValues := by
  constructor
  · intro S K
    funext n
    unfold typedList typedAddressListCodeBit
    rw [originalFields]
    cases decodeFields n <;> rfl
  · intro S K
    funext src cert dst
    unfold direct directMultisetCodeBit
    rw [originalFields,oneWitness]
    cases hx : decodeFields src <;> cases hw : decodeDirectWitness cert <;> cases hy : decodeFields dst <;> simp [lists]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmProof
