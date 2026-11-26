module
public import LogicLineages.StandardControlCurrent.InverseCutDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutTargets
open OrdinalComparison LayeredComparison.SnyatkovInverse InverseCut

def ActualLowerCuts : Prop := ∀ lo x : Nat,
  (lowerIndex Phi phiInverse lo ≤ x ↔ lo ≤ Phi x) ∧
  (lowerIndex FixedSeedControlResidue.H hyperInverse lo ≤ x ↔ lo ≤ FixedSeedControlResidue.H x)
def LeastResidue : Prop := ∀ a m r : Nat, 0 < m → r < m →
  a ≤ residueNext a m r ∧ residueNext a m r % m = r ∧
  ∀ x : Nat, a ≤ x → x % m = r → residueNext a m r ≤ x

def ActualCutElimination : Prop := ∀ p : Input,
  (answer Phi phiInverse p = true ↔
    0 < p.2.2.2.2.1 ∧ p.2.2.2.2.2 < p.2.2.2.2.1 ∧ Cut Phi p) ∧
  (answer FixedSeedControlResidue.H hyperInverse p = true ↔
    0 < p.2.2.2.2.1 ∧ p.2.2.2.2.2 < p.2.2.2.2.1 ∧ Cut FixedSeedControlResidue.H p)

def ActualPrograms : Prop :=
  Primrec (lowerIndex Phi phiInverse) ∧
  Primrec (lowerIndex FixedSeedControlResidue.H hyperInverse) ∧
  Primrec (fun p : Nat × Nat × Nat => residueNext p.1 p.2.1 p.2.2) ∧
  Primrec (candidate Phi phiInverse) ∧ Primrec (candidate FixedSeedControlResidue.H hyperInverse) ∧
  Primrec (answer Phi phiInverse) ∧ Primrec (answer FixedSeedControlResidue.H hyperInverse)

def Full : Prop := ActualLowerCuts ∧ LeastResidue ∧ ActualCutElimination ∧ ActualPrograms
end LogicLineages.StandardControlCurrent.InverseCutTargets
