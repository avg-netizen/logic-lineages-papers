module
public import LogicLineages.OrdinalComparison.ProfileDominatorDefinitions
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:direct (499–519): literal packed reserve eligibility below the
actual first maximum, uniformly in every genuine numerical retained mass. -/
def ActualProfileDirectPackedState : Prop :=
  ∀ L : NONote, (∃ ell : Ordinal.{0}, L.1.repr = Ordinal.omega0 ^ ell) →
    Ordinal.omega0 < L.1.repr → ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L.1.repr E →
    ∀ t c : Nat, profileDirectThreshold L E ≤ t → c + actualOrdinalNorm L.1.repr ≤ t →
      let word := profileBoundWord E
      let R := profileReserveBlocks word
      let pi := (profilePrincipalDominator word).1.repr
      let S := pi * ((R : Nat) : Ordinal) + (t : Ordinal)
      let Q := actualMaximumPredecessor L.1.repr (Phi t - c)
      S < L.1.repr ∧ S < epsilonZero ∧ actualOrdinalNorm S = R * actualOrdinalNorm pi + t ∧
      c + actualOrdinalNorm S < Phi t ∧ S ≤ Q ∧ actualOrdinalNorm S ≤ actualOrdinalNorm Q

end LogicLineages.OrdinalComparison.Targets
