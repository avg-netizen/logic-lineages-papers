module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical
/-- EXACT printed balanced threshold, with original coefficient mass C,
outside coefficient maximum C0, constant K, multiplier maximum A, complete
argument-offset maximum B and actual head-norm maximum N. -/
def threshold (K:Int) (C C0 A B N:Nat):Nat:=
  max 16 (max (2*C) (max (4*C0+4*K.natAbs+4) (max (A+B+2) (N+2))))
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical
