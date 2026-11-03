module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding

theorem typeParseRoundTrip (tau : Ty) : ∀ fuel,typeNumber tau<fuel → typeParse fuel (typeNumber tau)=some tau := by
  induction tau with
  | ground =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | arrow sigma tau ihs iht =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hs := Nat.left_le_pair (typeNumber sigma) (typeNumber tau)
      have ht := Nat.right_le_pair (typeNumber sigma) (typeNumber tau)
      simp only [typeNumber] at h
      have hsf : typeNumber sigma<fuel := by omega
      have htf : typeNumber tau<fuel := by omega
      rw [typeNumber,Nat.add_comm 1]
      simp [typeParse,ihs fuel hsf,iht fuel htf]

theorem typeNumericRoundTrip : NumberedNumericDecodingTargets.ActualTypeNumericRoundTrip := by
  intro tau
  simp [decodeType,typeParseRoundTrip tau (typeNumber tau+1) (by omega)]

theorem typeRoundTrip (tau : Ty) : decodeType (typeNumber tau)=some tau := typeNumericRoundTrip tau

theorem typesParseRoundTrip (types : List Ty) : ∀ fuel,typesNumber types<fuel → typesParse fuel (typesNumber types)=some types := by
  induction types with
  | nil =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons tau rest ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ht := Nat.right_le_pair (typeNumber tau) (typesNumber rest)
      simp only [typesNumber] at h
      have hrf : typesNumber rest<fuel := by omega
      rw [typesNumber,Nat.add_comm 1]
      simp [typesParse,typeRoundTrip,ih fuel hrf]

theorem typeListNumericRoundTrip : NumberedNumericDecodingTargets.ActualTypeListNumericRoundTrip := by
  intro types
  simp [decodeTypes,typesParseRoundTrip types (typesNumber types+1) (by omega)]

theorem typesRoundTrip (types : List Ty) : decodeTypes (typesNumber types)=some types := typeListNumericRoundTrip types

theorem headNumericRoundTrip {n : Nat} (head : HeadCode (Fin n)) : decodeHeadNumber n (headNumber head)=some head := by
  cases head <;> simp [decodeHeadNumber,headParse,headNumber,typeRoundTrip]

theorem payload_lt_tag (tag payload : Nat) (h : 0<tag) : payload<Nat.pair tag payload :=
  lt_of_le_of_lt (Nat.right_le_pair 0 payload) (Nat.pair_lt_pair_left payload h)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecodingSupportProof
