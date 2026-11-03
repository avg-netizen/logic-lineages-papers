module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalTargets
public import LogicLineages.OrdinalComparison.SparseSignedNumericalProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Proof

private theorem square_le_power (n:Nat) (hn:4≤n):n*n≤2^n:=by
  induction n,hn using Nat.le_induction with
  | base=>decide
  | succ n hn ih=>
    have hp:(n+1)*(n+1)≤2*(n*n):=by nlinarith
    calc
      (n+1)*(n+1)≤2*(n*n):=hp
      _≤2*2^n:=Nat.mul_le_mul_left 2 ih
      _=2^(n+1):=by rw [Nat.pow_succ,Nat.mul_comm]

theorem exactWindow:Targets.ExactWindowArithmetic:=by
  intro K C C0 A B N S s v hA hs hSs hsv hv
  have h16:16≤s:=(le_max_left _ _).trans hs
  have hrest:4*C0+4*K.natAbs+4≤s:=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
  have hab:A+B+2≤s:=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hs)))
  have hnorm:N+2≤s:=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hs)))
  have hvbound:v≤A*s+B:=hv.trans (Nat.add_le_add_right (Nat.mul_le_mul_left A hSs) B)
  have habs:(A+B+2)*s≤s*s:=Nat.mul_le_mul_right s hab
  have hBs:B≤B*s:=by nlinarith
  have hvquad:v<s*s:=by nlinarith
  have hsq:s*s≤2^s:=square_le_power s (by omega)
  have hexp:2^s≤Phi s:=
    (Nat.pow_le_pow_right (by decide) (by omega :s≤s+100)).trans (two_pow_shift_le_Phi s)
  have hlarge:4*C0+4*K.natAbs+4≤v:=hrest.trans hsv
  have hprod:(4*C0+4*K.natAbs+4)*v≤v*v:=Nat.mul_le_mul_right v hlarge
  have hv16:16≤v:=h16.trans hsv
  have hk:K.natAbs≤K.natAbs*v:=by
    simpa only [Nat.mul_one] using (Nat.mul_le_mul_left K.natAbs (show 1≤v by omega))
  refine ⟨hvquad,hvquad.trans_le (hsq.trans hexp),?_,hnorm⟩
  nlinarith
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Proof
