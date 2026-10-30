module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions
public import LogicLineages.OrdinalComparison.ActualOrdinalNormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 strict-mass proof718–737: actual equal-global first residuals and
literal child-domain inequality(7.7). B is a generic budget here; the final
source proof must derive the displayed budget bound from B=Phi t and T_L. -/
def ActualSuccessorMassResidualAlgebra : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma → Ordinal.omega0^gamma*Ordinal.omega0 < epsilonZero →
    ∀ B c e : Nat, c < e → e ≤ B → 2*actualOrdinalNorm (Ordinal.omega0^gamma) ≤ B-e →
      let theta := Ordinal.omega0^gamma
      let L := theta*Ordinal.omega0
      let w := actualOrdinalNorm theta
      let q := (B-e)/w
      let qc := (B-c)/w
      let re := actualMaximumPredecessor theta ((B-e)%w)
      let rc := actualMaximumPredecessor theta ((B-c)%w)
      let rhi := theta*((qc-q : Nat) : Ordinal)+rc
      0 < w ∧ 2 ≤ q ∧ q ≤ qc ∧ re < theta ∧ rhi < L ∧ re ≤ rhi ∧
      actualOrdinalNorm re ≤ actualOrdinalNorm rhi ∧
      e+q*w+actualOrdinalNorm re=B ∧ c+q*w+actualOrdinalNorm rhi=B ∧
      theta*(q : Ordinal)+re=actualMaximumPredecessor L (B-e) ∧
      theta*(q : Ordinal)+rhi=actualMaximumPredecessor L (B-c)

def ActualSuccessorMassChildDomains : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma → Ordinal.omega0^gamma*Ordinal.omega0 < epsilonZero →
    ∀ B c e : Nat, c < e → e ≤ B → 2*actualOrdinalNorm (Ordinal.omega0^gamma) ≤ B-e →
      let w := actualOrdinalNorm (Ordinal.omega0^gamma)
      let q := (B-e)/w
      ∀ j : Nat, 1 ≤ j → j ≤ q →
        c+w*(j-1) < e+w*(j-1) ∧ e+w*(j-1)+w ≤ B ∧ e+w*(j-1) ≤ B-w

end LogicLineages.OrdinalComparison.Targets
