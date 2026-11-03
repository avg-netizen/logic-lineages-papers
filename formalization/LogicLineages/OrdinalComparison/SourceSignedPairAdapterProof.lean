module
public import LogicLineages.OrdinalComparison.SourceSignedPairTargets
public import Mathlib.Data.Finsupp.SMul
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Proof

private theorem repeat_meaning {n} (x : Fin n → Ordinal) (d : Expression n) (k : Nat) :
    meaning x (repeatExpression d k) = (k : Int) • meaning x d := by
  induction k with
  | zero => simp [repeatExpression,zeroExpression,meaning]
  | succ k ih =>
    simp only [repeatExpression,meaning,ih,Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    exact add_comm _ _

private theorem shift_meaning {n} (x : Fin n → Ordinal) (d : Expression n) (k : Nat) :
    meaning x ((Expression.shift^[k]) d) = (omegaShift^[k]) (meaning x d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact congrArg omegaShift ih

private theorem monomial_meaning {n} (x : Fin n → Ordinal) (m : Monomial n) :
    meaning x (monomialExpression m) = monomialMeaning x m := by
  rcases m with ⟨c,p,u⟩
  cases c with
  | ofNat k =>
    have hk : ¬(Int.ofNat k<0) := by
      change ¬((k:Int)<0)
      exact not_lt_of_ge (Int.natCast_nonneg k)
    unfold monomialExpression monomialMeaning
    dsimp only
    rw [if_neg hk,repeat_meaning,shift_meaning]
    cases u <;> rfl
  | negSucc k =>
    have hk : Int.negSucc k<0 := by omega
    have hv : Int.negSucc k= -((k+1:Nat):Int) := by omega
    unfold monomialExpression monomialMeaning
    dsimp only
    rw [if_pos hk]
    simp only [meaning,repeat_meaning,shift_meaning]
    rw [hv,neg_smul]
    cases u <;> rfl

theorem monomialAdapter : Targets.MonomialAdapter := by
  intro n ms x
  induction ms with
  | nil => simp [fromMonomials,monomialsMeaning,zeroExpression,meaning]
  | cons m ms ih =>
    change meaning x (monomialExpression m) + meaning x (fromMonomials ms) =
      monomialMeaning x m + monomialsMeaning x ms
    rw [monomial_meaning,ih]
end LogicLineages.OrdinalComparison.Source.SignedPair.Proof
