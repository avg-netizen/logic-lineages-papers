module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericDecodingSupportProof

theorem typeNumericRoundTrip : NumberedNumericDecodingTargets.ActualTypeNumericRoundTrip := NumberedNumericDecodingSupportProof.typeNumericRoundTrip
theorem typeListNumericRoundTrip : NumberedNumericDecodingTargets.ActualTypeListNumericRoundTrip := NumberedNumericDecodingSupportProof.typeListNumericRoundTrip

theorem codeParseRoundTrip {n : Nat} (c : Code (Fin n)) : ∀ fuel,codeNumber c<fuel → codeParse n fuel (codeNumber c)=some c := by
  induction c with
  | var i =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [codeNumber,codeParse]
  | lam sigma body ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hp := payload_lt_tag 1 (Nat.pair (typeNumber sigma) (codeNumber body)) (by omega)
      have hb := Nat.right_le_pair (typeNumber sigma) (codeNumber body)
      simp only [codeNumber] at h
      have hf : codeNumber body<fuel := by omega
      simp [codeNumber,codeParse,typeRoundTrip,ih fuel hf]
  | app sigma q a ihq iha =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hp := payload_lt_tag 2 (Nat.pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a))) (by omega)
      have hb := Nat.right_le_pair (typeNumber sigma) (Nat.pair (codeNumber q) (codeNumber a))
      have hq := Nat.left_le_pair (codeNumber q) (codeNumber a)
      have ha := Nat.right_le_pair (codeNumber q) (codeNumber a)
      simp only [codeNumber] at h
      have hqf : codeNumber q<fuel := by omega
      have haf : codeNumber a<fuel := by omega
      simp [codeNumber,codeParse,typeRoundTrip,ihq fuel hqf,iha fuel haf]
  | bottom tau =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [codeNumber,codeParse,typeRoundTrip]
  | ordinary head base ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hp := payload_lt_tag 4 (Nat.pair (headNumber head) (codeNumber base)) (by omega)
      have hb := Nat.right_le_pair (headNumber head) (codeNumber base)
      simp only [codeNumber] at h
      have hf : codeNumber base<fuel := by omega
      simp [codeNumber,codeParse,headNumericRoundTrip,ih fuel hf]
  | numbered k head tau base types extras ihb ihe =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      let p4 := Nat.pair (typesNumber types) (codeNumber extras)
      let p3 := Nat.pair (codeNumber base) p4
      let p2 := Nat.pair (typeNumber tau) p3
      let p1 := Nat.pair (headNumber head) p2
      let payload := Nat.pair k p1
      have hp := payload_lt_tag 5 payload (by omega)
      have h1 := Nat.right_le_pair k p1
      have h2 := Nat.right_le_pair (headNumber head) p2
      have h3 := Nat.right_le_pair (typeNumber tau) p3
      have h4 := Nat.right_le_pair (codeNumber base) p4
      have hb := Nat.left_le_pair (codeNumber base) p4
      have he := Nat.right_le_pair (typesNumber types) (codeNumber extras)
      change Nat.pair 5 payload<fuel+1 at h
      have hbf : codeNumber base<fuel := by omega
      have hef : codeNumber extras<fuel := by omega
      simp [codeNumber,codeParse,headNumericRoundTrip,typeRoundTrip,typesRoundTrip,ihb fuel hbf,ihe fuel hef]
  | argumentsNil =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => simp [codeNumber,codeParse]
  | argumentsCons tau q rest ihq ihr =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hp := payload_lt_tag 7 (Nat.pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest))) (by omega)
      have hb := Nat.right_le_pair (typeNumber tau) (Nat.pair (codeNumber q) (codeNumber rest))
      have hq := Nat.left_le_pair (codeNumber q) (codeNumber rest)
      have hr := Nat.right_le_pair (codeNumber q) (codeNumber rest)
      simp only [codeNumber] at h
      have hqf : codeNumber q<fuel := by omega
      have hrf : codeNumber rest<fuel := by omega
      simp [codeNumber,codeParse,typeRoundTrip,ihq fuel hqf,ihr fuel hrf]

theorem codeNumericRoundTrip : NumberedNumericDecodingTargets.ActualCodeNumericRoundTrip := by
  intro n c
  simp [decodeCode,codeParseRoundTrip c (codeNumber c+1) (by omega)]

theorem codeRoundTrip (n : Nat) (c : Code (Fin n)) : decodeCode n (codeNumber c)=some c := codeNumericRoundTrip n c

theorem codeNumericSound : NumberedNumericDecodingTargets.ActualCodeNumericSound := by
  intro n value c h
  simp only [decodeCode,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

theorem packedNumericRoundTrip : NumberedNumericDecodingTargets.ActualPackedNumericRoundTrip := by
  intro n arity Gamma q
  have hp : decodePacked arity Gamma (q.1,termCode q.2)=some q :=
    NumberedAuxiliaryDecodingProof.packedRoundTrip (Fin n) arity Gamma q
  simp [decodePackedNumber,packedParse,packedNumber,typeRoundTrip,codeRoundTrip,hp]

theorem packedNumericSound : NumberedNumericDecodingTargets.ActualPackedNumericSound := by
  intro n arity Gamma value q h
  simp only [decodePackedNumber,Option.filter_eq_some_iff,decide_eq_true_eq] at h
  exact h.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingProof
