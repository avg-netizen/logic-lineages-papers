module
public import LogicLineages.OrdinalComparison.PositiveSourceDomainDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Actual nonzero-LIMIT source-head validity, not an NF-only surrogate. -/
def ActualPositiveHeadCodeDomain : Prop :=
  Primrec encodedPositiveHeadDomain ∧ ∀ rho : NONote,
    encodedPositiveHeadDomain (rawNoteEncode rho.1)=1 ↔
      Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero

/-- Genuine uniform numeric source validation and exact literal input
support, including invalid-headed TYPE-CORRECT trees. -/
def PositiveSourceDataProgram : Prop :=
  Primrec encodedPositiveSourceData ∧ ∀ E : FixedLimitPositiveExpr,
    ((encodedPositiveSourceData (positiveExprEncode E)).1=1 ↔ fixedLimitProfileBelow epsilonZero E) ∧
    (encodedPositiveSourceData (positiveExprEncode E)).2=(if positiveExprHasInput E then 1 else 0)

/-- Full all-Nat image characterization. A true numeric valid flag yields
an actual genuine original source tree, rather than a decoder-success premise. -/
def PositiveSourceDataImage : Prop :=
  ∀ n : Nat, (encodedPositiveSourceData n).1=1 ↔
    ∃ E : FixedLimitPositiveExpr, positiveExprEncode E=n ∧ fixedLimitProfileBelow epsilonZero E

end LogicLineages.OrdinalComparison.Targets
