module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.Admission
open Source Source.SyntaxCode

abbrev Input := Nat × List Nat × Nat

/-- Reuse the original numerical type checker at the current source node.
The traversal checks every actual node result type, extends the original
context only under lambda, and never normalizes or inserts unused context types. -/
def test (L : Nat) (Γ : List Nat) : Nat → Bool
  | n =>
    let current := (check Γ n).any (fun τ => decide (typeLevel τ ≤ L))
    current &&
      if h : n%8=5 ∨ n%8=6 then
        have hn : 0<n := by omega
        have hd : n/8<n := Nat.div_lt_self hn (by decide)
        let p := (n/8).unpair
        have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
        have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
        if n%8=5 then test L Γ p.1 && test L Γ p.2
        else test L (p.1::Γ) p.2
      else true
termination_by n => n
decreasing_by all_goals assumption

/-- Admission at the original fixed context and result type. Type codes are
the existing exact simple-type representation. -/
def typedAccepts (p : Input × Nat) : Bool :=
  test p.1.1 p.1.2.1 p.1.2.2 && decide (check p.1.2.1 p.1.2.2 = some p.2)

/-- The supported level-two class at the original all-ground free context.
Comparison mode does not change source admission. -/
def accepts (p : SourceCode.Input) : Bool :=
  test 2 (List.replicate p.1 0) p.2.2.1 &&
    test 2 (List.replicate p.1 0) p.2.2.2

/-- Guard the already checked source compiler. Rejected source inputs have
no output; accepted inputs are compiled by the exact same implementation. -/
def compile (p : SourceCode.Input) : Option Pair.Package :=
  if accepts p then SourceCode.compile p else none
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.Admission
