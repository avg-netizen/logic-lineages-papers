module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFieldsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCodeTargets
open NumberedWindowArithmeticCodecLaws NumberedWindowArithmeticFieldsProof

theorem fieldBelow (xs : List Nat) (x : Nat) (h : x ∈ xs) : x < encodeFields xs := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    change x < pair a (encodeFields xs) + 1
    rcases List.mem_cons.mp h with he | ht
    · rw [he]
      exact Nat.lt_succ_of_le (pairBounds a (encodeFields xs)).1
    · exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (ih ht))
        (pairBounds a (encodeFields xs)).2)

theorem nodeBelow (tag : Nat) (xs : List Nat) (x : Nat) (h : x ∈ xs) :
    x < encodeNode tag xs :=
  Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (fieldBelow xs x h))
    (pairBounds tag (encodeFields xs)).2)

theorem nodePos (tag : Nat) (xs : List Nat) : 0 < encodeNode tag xs := by
  simp only [encodeNode,Nat.zero_lt_succ]

theorem bounds : LiteralFieldBounds := ⟨fieldBelow,nodeBelow,nodePos⟩

theorem nodeRead {code tag : Nat} {xs : List Nat} (h : decodeNode code = some (tag,xs)) :
    encodeNode tag xs = code := by
  cases code with
  | zero => cases h
  | succ code =>
    cases hp : decode code with
    | none => simp [decodeNode,hp] at h
    | some pr =>
      obtain ⟨a,b⟩ := pr
      cases hb : decodeFields b with
      | none => simp [decodeNode,hp,hb] at h
      | some bs =>
        have e : (a,bs) = (tag,xs) :=
          Option.some.inj (by simpa [decodeNode,hp,hb] using h)
        obtain ⟨e₁,e₂⟩ := Prod.mk.inj e
        subst tag
        subst xs
        simp only [encodeNode,fieldsRead hb,pairRead hp]

theorem nodeRound (tag : Nat) (xs : List Nat) :
    decodeNode (encodeNode tag xs) = some (tag,xs) := by
  simp [encodeNode,decodeNode,pairRound,fieldsRound]

theorem exactCodec : ExactTaggedNodeCodec := by
  refine ⟨fun _ tag xs => ⟨nodeRead,fun h => h ▸ nodeRound tag xs⟩,nodeRound,?_⟩
  intro code
  constructor
  · intro h hImage
    obtain ⟨tag,xs,he⟩ := hImage
    have hr := nodeRound tag xs
    rw [he,h] at hr
    cases hr
  · intro h
    cases he : decodeNode code with
    | none => rfl
    | some p =>
      obtain ⟨tag,xs⟩ := p
      exact False.elim (h ⟨tag,xs,nodeRead he⟩)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof
