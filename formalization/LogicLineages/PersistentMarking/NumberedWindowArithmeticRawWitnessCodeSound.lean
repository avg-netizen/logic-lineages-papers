import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeSound
open NumberedWindowRawWitnessBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawRootCodeProof

private theorem assembleSound (child : Nat → Option RawWitness)
    (hs : ∀ n w, child n = some w → encodeWitness w = n)
    (tag : Nat) (xs : List Nat) (w : RawWitness)
    (h : assembleWitness child tag xs = some w) :
    encodeWitness w = encodeNode tag xs := by
  unfold assembleWitness at h
  split at h
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,rootSound _ _ hv]
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,hs _ _ hv]
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,hs _ _ hv]
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,hs _ _ hv]
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,hs _ _ hv]
  · obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [encodeWitness,hs _ _ hv]
  · cases h

theorem atFuel (fuel : Nat) : ∀ n w, decodeWitnessFuel fuel n = some w → encodeWitness w = n := by
  induction fuel with
  | zero => intro n w h; cases h
  | succ fuel ih =>
    intro n w h
    change (decodeNode n).bind (fun p => assembleWitness (decodeWitnessFuel fuel) p.1 p.2) =
      some w at h
    obtain ⟨p,hn,hw⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tag,xs⟩ := p
    exact (assembleSound (decodeWitnessFuel fuel) ih tag xs w hw).trans (nodeRead hn)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeSound
