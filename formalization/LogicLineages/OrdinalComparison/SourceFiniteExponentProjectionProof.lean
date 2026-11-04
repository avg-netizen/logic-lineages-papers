module
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionAlgebraProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Proof

theorem expressionTransport : Targets.ExpressionTransport := by
  intro n x d
  induction d with
  | unit =>
    rw [SignedPair.meaning]
    have h := SignedPair.Proof.cnf_nat 1
    simp only [Nat.cast_one] at h
    rw [h]
    ext k
    cases k with
    | zero => simp [polynomialMeaning,finitePart,Finsupp.single_apply]
    | succ k =>
      have hk : (0 : Ordinal.{0}) ≠ ((k+1 : Nat) : Ordinal.{0}) := by exact_mod_cast (Nat.zero_ne_add_one k)
      simp [polynomialMeaning,finitePart,Finsupp.single_apply,hk]
  | var i => rfl
  | add a b iha ihb =>
    change finitePart (SignedPair.meaning x a+SignedPair.meaning x b)=_
    rw [signedOperations.2.1,iha,ihb]
    rfl
  | neg a ih =>
    change finitePart (-SignedPair.meaning x a)=_
    rw [signedOperations.2.2.1,ih]
    rfl
  | shift a ih =>
    change finitePart (SignedPair.omegaShift (SignedPair.meaning x a))=_
    rw [exactShift,ih]
    rfl
end LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Proof
