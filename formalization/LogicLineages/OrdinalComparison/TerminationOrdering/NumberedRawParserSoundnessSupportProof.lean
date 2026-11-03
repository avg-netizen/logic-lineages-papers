module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessSupportProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding

theorem decodedType (value : Nat) (tau : Ty) (h : decodeType value=some tau) : typeNumber tau=value := by
  simp only [decodeType,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

theorem decodedTypes (value : Nat) (types : List Ty) (h : decodeTypes value=some types) : typesNumber types=value := by
  simp only [decodeTypes,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

theorem decodedHead (n value : Nat) (head : HeadCode (Fin n)) (h : decodeHeadNumber n value=some head) : headNumber head=value := by
  simp only [decodeHeadNumber,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

theorem typeSound (fuel : Nat) : ∀ value tau, typeParse fuel value=some tau → typeNumber tau=value := by
  induction fuel with
  | zero => intro value tau h; cases h
  | succ fuel ih =>
    intro value tau h
    cases value with
    | zero => cases h; rfl
    | succ value =>
      simp only [typeParse,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨sigma,hs,result,hr,rfl⟩ := h
      simp [typeNumber,ih _ _ hs,ih _ _ hr,Nat.add_comm]

theorem typesSound (fuel : Nat) : ∀ value types, typesParse fuel value=some types → typesNumber types=value := by
  induction fuel with
  | zero => intro value types h; cases h
  | succ fuel ih =>
    intro value types h
    cases value with
    | zero => cases h; rfl
    | succ value =>
      simp only [typesParse,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨tau,ht,rest,hr,rfl⟩ := h
      simp [typesNumber,decodedType _ _ ht,ih _ _ hr,Nat.add_comm]

theorem headSound (n value : Nat) (head : HeadCode (Fin n)) (h : headParse n value=some head) : headNumber head=value := by
  rcases hp : Nat.unpair value with ⟨tag,payload⟩
  have hv : Nat.pair tag payload=value := by simpa [hp] using Nat.pair_unpair value
  rcases tag with _ | _ | _ | _ | _ | _ | tag
  · simp [headParse,hp] at h
    obtain ⟨rfl,rfl⟩ := h
    exact hv
  · simp [headParse,hp] at h
    obtain ⟨rfl,rfl⟩ := h
    exact hv
  · simp only [headParse,hp,Option.map_eq_some_iff] at h
    obtain ⟨tau,ht,rfl⟩ := h
    simpa [headNumber,decodedType _ _ ht] using hv
  · simp only [headParse,hp,Option.map_eq_some_iff] at h
    obtain ⟨tau,ht,rfl⟩ := h
    simpa [headNumber,decodedType _ _ ht] using hv
  · simp only [headParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
    obtain ⟨sigma,hs,tau,ht,rfl⟩ := h
    simpa [headNumber,decodedType _ _ hs,decodedType _ _ ht] using hv
  · simp only [headParse,hp] at h
    split at h
    · cases h; exact hv
    · cases h
  · simp [headParse,hp] at h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessSupportProof
