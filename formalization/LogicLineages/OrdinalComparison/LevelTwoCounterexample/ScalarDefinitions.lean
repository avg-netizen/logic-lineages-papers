module
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionDefinitions
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceClassesFullTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample
open Source Source.ForwardTranslation Source.SourceClasses PolynomialGraphCompletion

/-- The actual canonical scalar's ordered original name occurrences. A repeated
source name remains the same name; no node allocation occurs in this adapter. -/
def scalarNames {ι : Type} : Scalar ι → List ι
  | .one => []
  | .var x => [x]
  | .add a b => scalarNames a ++ scalarNames b
  | .shift _ a => scalarNames a

/-- Direct adapter to the already checked polynomial graph grammar. The head
is the original normalized omega-natural-product head, not a new parameter. -/
def scalarExpr {ι : Type} (index : ι → Nat) : Scalar ι → Expr
  | .one => .numeral 1
  | .var x => .variable (index x)
  | .add a b => .add (scalarExpr index a) (scalarExpr index b)
  | .shift c a => .collapse (rawNoteEncode (scalarHeadNote c).1) (scalarExpr index a)

/-- Genuine polynomiality is a property of the actual source heads, not an
extra decision oracle or a replacement for the source internal-level bound. -/
def PolynomialScalar {ι : Type} (s : Scalar ι) : Prop :=
  ∀ c ∈ scalarHeads s, Order.IsSuccLimit (fixedHead c) ∧
    fixedHead c < Ordinal.omega0 ^ Ordinal.omega0

namespace ScalarCode
/-- Total radix conversion on all raw normalized source codes. Numeric
constants and head payloads retain their values; recursive children alone
are converted. Invalid source inputs acquire no source-correctness claim. -/
def lower (code : Nat) : Nat :=
  if code % 4 = 0 then 5 * (code / 4)
  else if code % 4 = 1 then 5 * (code / 4) + 1
  else if code % 4 = 2 then
    5 * Nat.pair (lower (code / 4).unpair.1) (lower (code / 4).unpair.2) + 2
  else 5 * Nat.pair (code / 4).unpair.1 (lower (code / 4).unpair.2) + 4
termination_by code
decreasing_by
  all_goals
    have hp : 0 < code := by omega
    have hd := Nat.div_lt_self hp (show 1 < 4 by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def lowerSyntax (code : Nat) : Nat := lower (normalizeScalarSyntaxCode code)
def package (code resultName : Nat) : ExpressionPackage :=
  ExpressionCode.package (lowerSyntax code) resultName
end ScalarCode
end LogicLineages.OrdinalComparison.LevelTwoCounterexample
