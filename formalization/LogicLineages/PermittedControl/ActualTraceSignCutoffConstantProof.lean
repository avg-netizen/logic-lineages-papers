module
public import LogicLineages.PermittedControl.ActualTraceSignCutoffTargets
import LogicLineages.PermittedControl.ActualZeroEdgeAlphabetProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof
import LogicLineages.PermittedControl.ActualSignedReadMassEdgeProof
import LogicLineages.PermittedControl.ActualZeroEdgeConstantShiftProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualTraceSignCutoff
open ActualReadChargeIteration ActualZeroEdgeAlphabet ActualFiniteGlobalTail
open ActualSignedReadMass ActualZeroEdgeConstantShift

private theorem traceSnoc {f : Nat → Nat} {B : Nat} {ρ : Nat → Nat} {r zRank n : Nat}
    {a b c : ReadState} (path : Trace f B ρ r zRank n a b) :
    ZeroEdge f B ρ r zRank b c → Trace f B ρ r zRank (n+1) a c := by
  induction path with
  | nil state =>
      intro edge
      exact .cons edge (.nil c)
  | cons first rest ih =>
      intro edge
      exact .cons first (ih edge)

private theorem depthBound {f : Nat → Nat} {B : Nat} {ρ : Nat → Nat} {r zRank n : Nat}
    {initial reached : ReadState} (path : Trace f B ρ r zRank n initial reached) :
    n ≤ syntaxCharge r (syntaxOf initial) := by
  have paid := (exactTraceAlphabet f B ρ r zRank n initial reached path).1
  rw [exactSyntaxCharge r initial]
  omega

theorem exactReachMassCeiling : ExactReachMassCeiling := by
  intro f B ρ r zRank n initial reached path
  have exponent : 3 ^ n ≤ 3 ^ syntaxCharge r (syntaxOf initial) :=
    Nat.pow_le_pow_right (by decide) (depthBound path)
  exact (exactTraceMass f B ρ r zRank n initial reached path).trans
    (Nat.mul_le_mul_right (signedMass initial.reads) exponent)

private theorem costSuffix (f : Nat → Nat) (B : Nat) (ρ : Nat → Nat) (r zRank : Nat)
    (initial : ReadState) {n : Nat} {first last : ReadState}
    (suffix : Trace f B ρ r zRank n first last) :
    ∀ depth, Trace f B ρ r zRank depth initial first →
      last.constant.natAbs ≤ first.constant.natAbs + n * stepCeiling r initial := by
  induction suffix with
  | nil s =>
      intro _ _
      simp
  | @cons k a b c edge tail ih =>
      intro depth reached
      have following := traceSnoc reached edge
      have rest := ih (depth+1) following
      let alphabet := globalAlphabet r (syntaxOf initial)
      have coverage := exactGlobalLabelEnclosure f B ρ r zRank depth initial a reached
      have edgeCost := (exactActualConstantShift f B ρ r zRank a b alphabet edge coverage).2
      have mass := exactReachMassCeiling f B ρ r zRank depth initial a reached
      have increment : b.constant.natAbs ≤ a.constant.natAbs + stepCeiling r initial :=
        edgeCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (edgeFactor alphabet) mass) _)
      calc
        c.constant.natAbs ≤ b.constant.natAbs + k * stepCeiling r initial := rest
        _ ≤ (a.constant.natAbs + stepCeiling r initial) + k * stepCeiling r initial :=
          Nat.add_le_add_right increment _
        _ = a.constant.natAbs + (k+1) * stepCeiling r initial := by
          rw [Nat.add_mul,Nat.one_mul]
          ac_rfl

theorem exactTraceConstantCeiling : ExactTraceConstantCeiling := by
  intro f B ρ r zRank n initial reached path
  have signed := costSuffix f B ρ r zRank initial path 0 (.nil initial)
  exact ⟨signed,signed.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (depthBound path)) _)⟩

end LogicLineages.PermittedControl.ActualTraceSignCutoff
