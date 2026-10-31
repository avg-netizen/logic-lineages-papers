module
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- Raw scalar-source syntax code. Shift heads contain literal positive AST
codes, not already-normalized ordinal notes. -/
def scalarSyntaxCode {ι : Type} (index : ι → Nat) : Scalar ι → Nat
  | .one => 4
  | .var x => 4 * index x + 1
  | .add a b => 4 * Nat.pair (scalarSyntaxCode index a) (scalarSyntaxCode index b) + 2
  | .shift c a => 4 * Nat.pair (closedPositiveCode c) (scalarSyntaxCode index a) + 3

/-- Uniform numeric source-head normalization. Only syntactic tags and the
proved actual encoded closed-positive evaluator are used. -/
def normalizeScalarSyntaxCode : Nat → Nat
  | n =>
    if h0 : n % 4 = 0 then n
    else if h1 : n % 4 = 1 then n
    else
      have hn : 0 < n := by omega
      have hd : n / 4 < n := Nat.div_lt_self hn (by decide)
      let p := (n / 4).unpair
      have hl : p.1 < n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2 < n := (Nat.unpair_right_le _).trans_lt hd
      if n % 4 = 2 then
        4 * Nat.pair (normalizeScalarSyntaxCode p.1) (normalizeScalarSyntaxCode p.2) + 2
      else 4 * Nat.pair (encodedClosedHead p.1) (normalizeScalarSyntaxCode p.2) + 3
termination_by n => n
decreasing_by all_goals assumption

noncomputable def scalarSyntaxValue (n : Nat) (xs : List Nat) : Nat :=
  encodedScalarValue (normalizeScalarSyntaxCode n) xs
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
