module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Targets
open CommonHeadLargeRow
/-- Source balanced-L numerical window/remainder estimate. S is the ENTIRE
shared-basis sum, s the minimum COMPLETE norm input and v any surviving input.
The list/certificate consumers must still derive S≤s and v≤A*S+B from ALL
positive coefficients; these are explicit numerical inputs, not paid consumers. -/
def ExactWindowArithmetic:Prop:=∀K:Int,∀C C0 A B N S s v:Nat,
  1≤A→threshold K C C0 A B N≤s→S≤s→s≤v→v≤A*S+B→
  v<s*s∧v<Phi s∧4*(K.natAbs+C0*v)<v*v∧N+2≤s
/-- Sparse endpoint sign with an OPEN actual lower-layer remainder R. The
remainder bound is measured against the SELECTED SURVIVING block, never a
possibly cancelled maximum. It replaces the common-head constant-size bound;
all numerical bands/spacing/mass are explicit and must be paid by actual heads. -/
def SurvivingRemainderDominance:Prop:=∀R:Int,∀row:NumericalRow,
  row.Pairwise (fun a b=>a.2.2≠b.2.2)→
  (∀a∈row,max 4 (2*numericalMass row)≤a.2.2∧Phi a.2.2<a.2.1∧a.2.1<2*Phi a.2.2)→
  ∀a∈row,a.1≠0→(∀b∈row,b.2.2≤a.2.2)→4*R.natAbs<Phi a.2.2→
    Int.sign (numericalValue R row)=Int.sign a.1
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumerical.Targets
