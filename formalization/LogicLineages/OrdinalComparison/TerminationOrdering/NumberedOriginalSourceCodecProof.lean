module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedNumericDecoding NumberedLeastCodeRepresentative
open NumberedOriginalAngle NumberedOriginalSourceCodec

theorem transportSelf {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (h : tau=tau) (q : AuxTerm Symbol arity Gamma tau) : transportAux h q=q := by
  have he : h=rfl := Subsingleton.elim _ _
  rw [he]
  rfl

theorem projectionRoundTrip : NumberedOriginalSourceCodecTargets.ActualProjectionRoundTrip :=
  NumberedOriginalSourceCodecSupportProof.projectionRoundTrip

theorem projectionSound : NumberedOriginalSourceCodecTargets.ActualProjectionSound :=
  NumberedOriginalSourceCodecSupportProof.projectionSound

theorem argumentProjectionRoundTrip : NumberedOriginalSourceCodecTargets.ActualArgumentProjectionRoundTrip :=
  NumberedOriginalSourceCodecSupportProof.argumentProjectionRoundTrip

theorem projectionImage : NumberedOriginalSourceCodecTargets.ActualProjectionImage := by
  intro Symbol arity Gamma tau q
  constructor
  · intro h
    cases hp : project q with
    | none => simp only [hp,Option.isSome_none,Bool.false_eq_true] at h
    | some s => exact ⟨s,(projectionSound Symbol arity Gamma tau q s hp).symm⟩
  · rintro ⟨s,rfl⟩
    rw [projectionRoundTrip Symbol arity Gamma tau s]
    rfl

theorem numericRoundTrip : NumberedOriginalSourceCodecTargets.ActualNumericRoundTrip := by
  intro n arity Gamma tau s
  unfold sourceNumber decodeSourceNumber
  rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
  change (if h : tau=tau then project (transportAux h (translateOriginal s)) else none)=some s
  rw [dif_pos rfl,transportSelf]
  exact projectionRoundTrip (Fin n) arity Gamma tau s

theorem numericSound : NumberedOriginalSourceCodecTargets.ActualNumericSound := by
  intro n arity Gamma tau value s h
  cases hd : decodePackedNumber n arity Gamma value with
  | none => simp only [decodeSourceNumber,hd,Option.bind_eq_bind,Option.bind_none] at h; cases h
  | some q =>
    have hs : (if he : q.1=tau then project (transportAux he q.2) else none)=some s := by
      simpa only [decodeSourceNumber,hd,Option.bind_eq_bind,Option.bind_some] using h
    by_cases he : q.1=tau
    · rw [dif_pos he] at hs
      have hpacked : (⟨tau,translateOriginal s⟩ : Packed (Fin n) arity Gamma)=q := by
        rcases q with ⟨sigma,Q⟩
        dsimp only at he
        cases he
        have hQ : translateOriginal s=Q := projectionSound (Fin n) arity Gamma _ Q s (by simpa only [transportSelf] using hs)
        exact congrArg (fun q => (⟨_,q⟩ : Packed (Fin n) arity Gamma)) hQ
      unfold sourceNumber
      rw [hpacked]
      exact NumberedNumericDecodingProof.packedNumericSound n arity Gamma value q hd
    · rw [dif_neg he] at hs
      cases hs

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceCodecProof
