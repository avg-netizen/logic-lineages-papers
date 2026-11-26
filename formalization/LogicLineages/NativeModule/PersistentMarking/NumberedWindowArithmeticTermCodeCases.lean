module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticNodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticHeadCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeCases
open NumberedWindowSyntax
open NumberedWindowArithmeticPair (pair)
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticCodecLaws NumberedWindowArithmeticNodeProof

abbrev GoodTerm (fuel : Nat) : Prop :=
  ∀ Q, encodeTerm Q ≤ fuel → decodeTermFuel fuel (encodeTerm Q) = some Q

abbrev GoodArgs (fuel : Nat) : Prop :=
  ∀ qs, encodeArgs qs ≤ fuel → decodeArgsFuel fuel (encodeArgs qs) = some qs

private theorem childFuel (tag : Nat) (fields : List Nat) (x fuel : Nat)
    (h : encodeNode tag fields ≤ fuel+1) (hx : x ∈ fields) : x ≤ fuel :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (nodeBelow tag fields x hx) h)

theorem termStep (fuel : Nat) (it : GoodTerm fuel) (ia : GoodArgs fuel) :
    GoodTerm (fuel+1) := by
  intro Q hm
  cases Q with
  | free σ x =>
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticTyCodeProof.roundtrip]
  | bound σ i =>
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticTyCodeProof.roundtrip]
  | lam σ Q =>
    have hQ := it Q (childFuel 2 [encodeTy σ,encodeTerm Q] (encodeTerm Q) fuel hm (by simp))
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticTyCodeProof.roundtrip,hQ]
  | bottom σ =>
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticTyCodeProof.roundtrip]
  | ordinary f bs =>
    have hb := ia bs (childFuel 4 [encodeHead f,encodeArgs bs] (encodeArgs bs) fuel hm (by simp))
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticHeadCodeProof.roundtrip,hb]
  | numbered f τ k bs es =>
    let fs := [encodeHead f,encodeTy τ,k,encodeArgs bs,encodeArgs es]
    have hb := ia bs (childFuel 5 fs (encodeArgs bs) fuel hm (by simp [fs]))
    have he := ia es (childFuel 5 fs (encodeArgs es) fuel hm (by simp [fs]))
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticHeadCodeProof.roundtrip,
      NumberedWindowArithmeticTyCodeProof.roundtrip,hb,he]
  | auxApp σ τ Q A =>
    let fs := [encodeTy σ,encodeTy τ,encodeTerm Q,encodeTerm A]
    have hQ := it Q (childFuel 6 fs (encodeTerm Q) fuel hm (by simp [fs]))
    have hA := it A (childFuel 6 fs (encodeTerm A) fuel hm (by simp [fs]))
    simp [encodeTerm,decodeTermFuel,nodeRound,assemble,NumberedWindowArithmeticTyCodeProof.roundtrip,hQ,hA]

theorem argsStep (fuel : Nat) (it : GoodTerm fuel) (ia : GoodArgs fuel) :
    GoodArgs (fuel+1) := by
  intro qs hm
  cases qs with
  | nil => rfl
  | cons Q qs =>
    have hr : pair (encodeTerm Q) (encodeArgs qs) ≤ fuel := Nat.le_of_succ_le_succ hm
    have hb := pairBounds (encodeTerm Q) (encodeArgs qs)
    have hQ := it Q (Nat.le_trans hb.1 hr)
    have hqs := ia qs (Nat.le_trans hb.2 hr)
    simp [encodeArgs,decodeArgsFuel,pairRound,hQ,hqs]

theorem termPositive (Q : NTerm) : 0 < encodeTerm Q := by
  cases Q <;> exact nodePos _ _

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeCases
