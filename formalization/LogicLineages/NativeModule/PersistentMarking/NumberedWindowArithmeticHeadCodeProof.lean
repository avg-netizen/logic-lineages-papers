module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTyCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCodeProof
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticAtomCodeTargets NumberedWindowArithmeticCodecLaws

private theorem partsSound : ∀ tag p f,
    decodeHeadParts tag p = some f → encodeHead f = pair tag p
  | 0,0,f,h => by
    have e : Head.zero = f := Option.some.inj h
    subst f
    rfl
  | 0,p+1,f,h => by cases h
  | 1,0,f,h => by
    have e : Head.succ = f := Option.some.inj h
    subst f
    rfl
  | 1,p+1,f,h => by cases h
  | 2,p,f,h => by
    have hh : (decodeTy p).map Head.case = some f := h
    obtain ⟨τ,ht,rfl⟩ := Option.map_eq_some_iff.mp hh
    simp only [encodeHead,NumberedWindowArithmeticTyCodeProof.decodeSound ht]
  | 3,p,f,h => by
    have hh : (decodeTy p).map Head.recursor = some f := h
    obtain ⟨τ,ht,rfl⟩ := Option.map_eq_some_iff.mp hh
    simp only [encodeHead,NumberedWindowArithmeticTyCodeProof.decodeSound ht]
  | 4,p,f,h => by
    cases hp : decode p with
    | none => simp [decodeHeadParts,hp] at h
    | some pr =>
      obtain ⟨a,b⟩ := pr
      cases ha : decodeTy a with
      | none => simp [decodeHeadParts,hp,ha] at h
      | some A =>
        cases hb : decodeTy b with
        | none => simp [decodeHeadParts,hp,ha,hb] at h
        | some B =>
          have e : Head.app A B = f :=
            Option.some.inj (by simpa [decodeHeadParts,hp,ha,hb] using h)
          subst f
          simp only [encodeHead,NumberedWindowArithmeticTyCodeProof.decodeSound ha,
            NumberedWindowArithmeticTyCodeProof.decodeSound hb,pairRead hp]
  | 5,p,f,h => by
    have hh : (decode p).map (fun q => Head.ranked q.1 q.2) = some f := h
    obtain ⟨q,hq,rfl⟩ := Option.map_eq_some_iff.mp hh
    obtain ⟨a,b⟩ := q
    simp only [encodeHead,pairRead hq]
  | tag+6,p,f,h => by cases h

theorem decodeSound {n : Nat} {f : Head} (h : decodeHead n = some f) :
    encodeHead f = n := by
  have hbind : (decode n).bind (fun q => decodeHeadParts q.1 q.2) = some f := h
  obtain ⟨q,hq,hf⟩ := Option.bind_eq_some_iff.mp hbind
  obtain ⟨tag,payload⟩ := q
  exact (partsSound tag payload f hf).trans (pairRead hq)

theorem roundtrip (f : Head) : decodeHead (encodeHead f) = some f := by
  cases f <;> simp [decodeHead,encodeHead,decodeHeadParts,pairRound,
    NumberedWindowArithmeticTyCodeProof.roundtrip]

theorem exactCodec : ExactHeadCodec :=
  codec encodeHead decodeHead (fun _ _ h => decodeSound h) roundtrip

end LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCodeProof
