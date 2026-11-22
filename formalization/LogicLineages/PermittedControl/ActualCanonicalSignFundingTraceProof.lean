module
public import LogicLineages.PermittedControl.ActualCanonicalSignFundingTargets
import LogicLineages.PermittedControl.ActualCanonicalSignFundingMassProof
import LogicLineages.PermittedControl.ActualCanonicalSignFundingShiftProof
import LogicLineages.PermittedControl.ActualCanonicalZeroTraceReplayProof
import LogicLineages.PermittedControl.ActualCanonicalReachedFundingTraceProof
import LogicLineages.PermittedControl.ActualFiniteGlobalTailEnclosureProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalSignFunding
open OrdinalComparison
open ActualReadChargeIteration (ReadState stateCharge RankBound)
open ActualZeroClassReplacement
open ActualCanonicalZeroTrace ActualCanonicalReachedFunding
open ActualFiniteGlobalTail ActualTraceSignCutoff ActualSignedReadMass ActualZeroEdgeConstantShift
open ActualFullLabelPairGuards (Answer)

private theorem snoc {f B ρ r top answers s t u a}
    (path : CanonicalTrace f B ρ r top answers s t) :
    CanonicalZeroWitness f B ρ r top t u a →
    CanonicalTrace f B ρ r top (answers ++ [a]) s u := by
  induction path with
  | nil s =>
    intro edge
    exact .cons edge (.nil u)
  | cons head tail ih =>
    intro edge
    exact .cons head (ih edge)

private theorem depthBound {f B ρ r top answers initial reached}
    (selected : SelectedWithThreshold f B)
    (path : CanonicalTrace f B ρ r top answers initial reached) :
    answers.length ≤ syntaxCharge r (syntaxOf initial) := by
  have paid := (exactCanonicalTraceReplay f B selected ρ r top initial reached answers path).2.2.2.2.2
  rw [exactSyntaxCharge r initial]
  omega

private theorem traceMass {f B ρ r top answers s t}
    (path : CanonicalTrace f B ρ r top answers s t) :
    signedMass t.reads ≤ 3 ^ answers.length * signedMass s.reads := by
  induction path with
  | nil s => simp
  | @cons a answers s t u edge rest ih =>
    calc
      signedMass u.reads ≤ 3 ^ answers.length * signedMass t.reads := ih
      _ ≤ 3 ^ answers.length * (3 * signedMass s.reads) :=
        Nat.mul_le_mul_left _ (exactCanonicalEdgeMass f B ρ r top s t a edge)
      _ = 3 ^ (a::answers).length * signedMass s.reads := by
        rw [List.length_cons,Nat.pow_succ,Nat.mul_assoc]

theorem exactCanonicalTraceMass : ExactCanonicalTraceMass := by
  intro f B selected ρ r top initial reached answers path
  have exponent : 3 ^ answers.length ≤ 3 ^ syntaxCharge r (syntaxOf initial) :=
    Nat.pow_le_pow_right (by decide) (depthBound selected path)
  exact ⟨traceMass path,(traceMass path).trans
    (Nat.mul_le_mul_right (signedMass initial.reads) exponent)⟩

private theorem costSuffix (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (r top : Nat) (initial : ReadState)
    (live : liftedReads f ρ initial.reads) (ranked : RankBound r top initial) (long : LongState initial)
    {answers : List (List Answer)} {first last : ReadState}
    (suffix : CanonicalTrace f B ρ r top answers first last) :
    ∀ seen, CanonicalTrace f B ρ r top seen initial first →
      last.constant.natAbs ≤ first.constant.natAbs + answers.length * stepCeiling r initial := by
  induction suffix with
  | nil s =>
    intro _ _
    simp
  | @cons a tail s t u edge rest ih =>
    intro seen reached
    have following := snoc reached edge
    have remain := ih (seen ++ [a]) following
    let alphabet := globalAlphabet r (syntaxOf initial)
    have coverage := (exactCanonicalReachFacts f B selected ρ r top initial s seen
      live ranked long reached).2.2.2.2
    have edgeCost := (exactCanonicalShift f B ρ r top s t a alphabet edge coverage).2
    have mass := (exactCanonicalTraceMass f B selected ρ r top initial s seen reached).2
    have increment : t.constant.natAbs ≤ s.constant.natAbs + stepCeiling r initial :=
      edgeCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (edgeFactor alphabet) mass) _)
    calc
      u.constant.natAbs ≤ t.constant.natAbs + tail.length * stepCeiling r initial := remain
      _ ≤ (s.constant.natAbs + stepCeiling r initial) + tail.length * stepCeiling r initial :=
        Nat.add_le_add_right increment _
      _ = s.constant.natAbs + (a::tail).length * stepCeiling r initial := by
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        ac_rfl

theorem exactCanonicalTraceConstant : ExactCanonicalTraceConstant := by
  intro f B selected ρ r top initial reached answers live ranked long path
  have bound := costSuffix f B selected ρ r top initial live ranked long path [] (.nil initial)
  exact ⟨bound,bound.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (depthBound selected path)) _)⟩

end LogicLineages.PermittedControl.ActualCanonicalSignFunding
