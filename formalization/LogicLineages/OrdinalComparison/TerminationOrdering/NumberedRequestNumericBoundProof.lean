module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedRequestWeight

theorem codeWeightBound : NumberedRequestNumericBoundTargets.ActualCodeWeightBound := by
  intro n code
  induction code with
  | var index =>
    simp only [codeWeight]
    omega
  | lam sigma body ih =>
    have hp := Nat.add_le_pair 1 (Nat.pair (typeNumber sigma) (codeNumber body))
    have hb := Nat.right_le_pair (typeNumber sigma) (codeNumber body)
    simp only [codeWeight, codeNumber]
    omega
  | app sigma q a ihq iha =>
    have hp := Nat.add_le_pair 2
      (Nat.pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a)))
    have hb := Nat.right_le_pair (typeNumber sigma)
      (Nat.pair (codeNumber q) (codeNumber a))
    have hc := Nat.add_le_pair (codeNumber q) (codeNumber a)
    simp only [codeWeight, codeNumber]
    omega
  | bottom tau =>
    simp only [codeWeight]
    omega
  | ordinary head base ih =>
    have hp := Nat.add_le_pair 4 (Nat.pair (headNumber head) (codeNumber base))
    have hb := Nat.right_le_pair (headNumber head) (codeNumber base)
    simp only [codeWeight, codeNumber]
    omega
  | numbered k head tau base types extras ihb ihe =>
    let p4 := Nat.pair (typesNumber types) (codeNumber extras)
    let p3 := Nat.pair (codeNumber base) p4
    let p2 := Nat.pair (typeNumber tau) p3
    let p1 := Nat.pair (headNumber head) p2
    let payload := Nat.pair k p1
    have hp := Nat.add_le_pair 5 payload
    have h1 := Nat.right_le_pair k p1
    have h2 := Nat.right_le_pair (headNumber head) p2
    have h3 := Nat.right_le_pair (typeNumber tau) p3
    have hb := Nat.add_le_pair (codeNumber base) p4
    have he := Nat.right_le_pair (typesNumber types) (codeNumber extras)
    change 1 + codeWeight base + codeWeight extras ≤ Nat.pair 5 payload + 1
    omega
  | argumentsNil =>
    simp only [codeWeight]
    omega
  | argumentsCons tau q rest ihq ihr =>
    have hp := Nat.add_le_pair 7
      (Nat.pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest)))
    have hb := Nat.right_le_pair (typeNumber tau)
      (Nat.pair (codeNumber q) (codeNumber rest))
    have hc := Nat.add_le_pair (codeNumber q) (codeNumber rest)
    simp only [codeWeight, codeNumber]
    omega

theorem codeFuelPrimitive : NumberedRequestNumericBoundTargets.ActualCodeFuelPrimitive := by
  intro n
  exact Primrec.succ.comp (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundProof
