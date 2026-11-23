module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticReplacementCodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticBinderCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof
open NumberedWindowRawWitnessRootBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticRawRootCode NumberedWindowArithmeticReplacementCodeProof

private theorem assembleSound (tag : Nat) (xs : List Nat) (w : RawRootWitness)
    (h : assembleRoot tag xs = some w) : encodeRoot w = encodeNode tag xs := by
  unfold assembleRoot at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨b,hb,dom,hd,rfl⟩ := h
    simp only [encodeRoot,flagSound _ _ hb,NumberedWindowArithmeticBinderCodeProof.decodeSound hd]
  · cases h; rfl
  · obtain ⟨replacement,hr,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeRoot,partSound _ _ hr]
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem rootSound (n : Nat) (w : RawRootWitness) (h : decodeRoot n = some w) :
    encodeRoot w = n := by
  change (decodeNode n).bind (fun p => assembleRoot p.1 p.2) = some w at h
  obtain ⟨p,hn,hw⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tag,xs⟩ := p
  exact (assembleSound tag xs w hw).trans (nodeRead hn)

theorem rootRound (w : RawRootWitness) : decodeRoot (encodeRoot w) = some w := by
  cases w <;> simp [decodeRoot,encodeRoot,nodeRound,assembleRoot,flagRound,
    NumberedWindowArithmeticBinderCodeProof.roundtrip,partRound]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof
