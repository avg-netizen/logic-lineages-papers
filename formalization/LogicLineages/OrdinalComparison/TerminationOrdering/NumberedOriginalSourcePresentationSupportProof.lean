module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedOriginalAngle
open NumberedOriginalSourceCodec NumberedOriginalSourcePresentation

theorem packedRoundTrip : NumberedOriginalSourcePresentationTargets.ActualPackedRoundTrip := by
  intro n arity Gamma p
  rcases p with ⟨tau,s⟩
  unfold decodePackedSourceNumber packedSourceNumber sourceNumber
  rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
  simp only [Option.bind_eq_bind,Option.bind_some]
  rw [NumberedOriginalSourceCodecProof.projectionRoundTrip]
  rfl

theorem packedSound : NumberedOriginalSourcePresentationTargets.ActualPackedSound := by
  intro n arity Gamma value p h
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp only [decodePackedSourceNumber,hd,Option.bind_eq_bind,Option.bind_none] at h; cases h
  | some q =>
    rcases q with ⟨tau,Q⟩
    change ((decodePackedNumber n arity Gamma value).bind (fun q =>
      (project q.2).bind (fun s => some ⟨q.1,s⟩)))=some p at h
    rw [hd] at h
    simp only [Option.bind_some] at h
    cases hp : project Q with
    | none => simp only [hp,Option.bind_none] at h; cases h
    | some s =>
      rw [hp] at h
      simp only [Option.bind_some,Option.some.injEq] at h
      subst p
      have hs := NumberedOriginalSourceCodecProof.projectionSound (Fin n) arity Gamma tau Q s hp
      change packedNumber ⟨tau,NumberedRewriteSyntax.translateOriginal s⟩=value
      rw [hs]
      exact NumberedNumericDecodingProof.packedNumericSound n arity Gamma value ⟨tau,Q⟩ hd

theorem rawShapeOfDecoded (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat)
    (q : Packed (Fin n) arity Gamma) (h : decodePackedNumber n arity Gamma value=some q) :
    rawSourceShape n value=(project q.2).isSome := by
  have hv := NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q h
  rw [←hv]
  simp only [rawSourceShape,packedNumber,Nat.unpair_pair]
  rw [NumberedNumericDecodingProof.codeRoundTrip]
  exact (NumberedOriginalSourceShapeProof.termShape (Fin n) arity Gamma q.1 q.2).symm

theorem packedValidity : NumberedOriginalSourcePresentationTargets.ActualPackedValidity := by
  intro n arity Gamma value
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp only [packedSourceTest,hd,Option.isSome_none,Bool.false_and,
      decodePackedSourceNumber,Option.bind_eq_bind,Option.bind_none,Option.isSome_none]
  | some q =>
    rw [packedSourceTest,hd,Option.isSome_some,Bool.true_and,rawShapeOfDecoded n arity Gamma value q hd]
    change (project q.2).isSome=((decodePackedNumber n arity Gamma value).bind
      (fun q => (project q.2).bind (fun s => some (⟨q.1,s⟩ : PackedSource (Fin n) arity Gamma)))).isSome
    rw [hd,Option.bind_some]
    exact (NumberedOriginalSourceShapeProof.pureBindIsSome (project q.2)
      (fun s => (⟨q.1,s⟩ : PackedSource (Fin n) arity Gamma))).symm

theorem typeNumberInjective : Function.Injective typeNumber := by
  intro sigma tau h
  have h' := congrArg decodeType h
  rw [NumberedNumericDecodingProof.typeNumericRoundTrip,NumberedNumericDecodingProof.typeNumericRoundTrip] at h'
  exact Option.some.inj h'

theorem fixedValidity : NumberedOriginalSourcePresentationTargets.ActualFixedValidity := by
  intro n arity Gamma tau value
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp only [sourceTest,packedSourceTest,hd,Option.isSome_none,Bool.false_and,
      decodeSourceNumber,Option.bind_eq_bind,Option.bind_none,Option.isSome_none]
  | some q =>
    rcases q with ⟨sigma,Q⟩
    have hv := NumberedNumericDecodingProof.packedNumericSound n arity Gamma value ⟨sigma,Q⟩ hd
    have htype : (Nat.unpair value).1=typeNumber sigma := by
      rw [←hv]
      simp only [packedNumber,Nat.unpair_pair]
    have hshape := rawShapeOfDecoded n arity Gamma value ⟨sigma,Q⟩ hd
    by_cases ht : sigma=tau
    · subst tau
      simp [sourceTest,packedSourceTest,hd,htype,hshape,decodeSourceNumber,
        NumberedOriginalSourceCodecProof.transportSelf]
    · have hn : typeNumber sigma≠typeNumber tau := fun he => ht (typeNumberInjective he)
      simp [sourceTest,packedSourceTest,hd,htype,hn,decodeSourceNumber,ht]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationSupportProof
