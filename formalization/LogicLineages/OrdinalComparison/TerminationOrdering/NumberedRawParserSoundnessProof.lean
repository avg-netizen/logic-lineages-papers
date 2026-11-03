module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedRawParserSoundnessSupportProof

theorem rawTypeSound : NumberedRawParserSoundnessTargets.ActualRawTypeSound := typeSound
theorem rawTypeListSound : NumberedRawParserSoundnessTargets.ActualRawTypeListSound := typesSound
theorem rawHeadSound : NumberedRawParserSoundnessTargets.ActualRawHeadSound := headSound

theorem rawCodeSound : NumberedRawParserSoundnessTargets.ActualRawCodeSound := by
  intro n fuel
  induction fuel with
  | zero => intro value code h; cases h
  | succ fuel ih =>
    intro value code h
    rcases hp : Nat.unpair value with ⟨tag,payload⟩
    have hv : Nat.pair tag payload=value := by simpa [hp] using Nat.pair_unpair value
    rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | tag
    · simp only [codeParse,hp,Option.some.injEq] at h
      cases h; exact hv
    · simp only [codeParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨sigma,hs,body,hb,rfl⟩ := h
      simpa [codeNumber,decodedType _ _ hs,ih _ _ hb] using hv
    · simp only [codeParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨sigma,hs,q,hq,a,ha,rfl⟩ := h
      simpa [codeNumber,decodedType _ _ hs,ih _ _ hq,ih _ _ ha] using hv
    · simp only [codeParse,hp,Option.map_eq_some_iff] at h
      obtain ⟨tau,ht,rfl⟩ := h
      simpa [codeNumber,decodedType _ _ ht] using hv
    · simp only [codeParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨head,hh,base,hb,rfl⟩ := h
      simpa [codeNumber,decodedHead _ _ _ hh,ih _ _ hb] using hv
    · simp only [codeParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨head,hh,tau,ht,base,hb,types,hs,extras,he,rfl⟩ := h
      simpa [codeNumber,decodedHead _ _ _ hh,decodedType _ _ ht,decodedTypes _ _ hs,ih _ _ hb,ih _ _ he] using hv
    · simp [codeParse,hp] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hv
    · simp only [codeParse,hp,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨tau,ht,q,hq,rest,hr,rfl⟩ := h
      simpa [codeNumber,decodedType _ _ ht,ih _ _ hq,ih _ _ hr] using hv
    · simp [codeParse,hp] at h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRawParserSoundnessProof
