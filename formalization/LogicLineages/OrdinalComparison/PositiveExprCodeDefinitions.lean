module
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions
public import LogicLineages.OrdinalComparison.RawNormalProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Faithful numeric interface for the unchanged literal P1 source AST. -/
def positiveExprEncode : FixedLimitPositiveExpr → Nat
  | .constant n => 4*n
  | .input => 1
  | .add E F => 4*Nat.pair (positiveExprEncode E) (positiveExprEncode F)+2
  | .head rho E => 4*Nat.pair (rawNoteEncode rho.1) (positiveExprEncode E)+3

/-- Total parser with explicit invalid-input behavior. Head codes are checked
by the existing exact normal-notation predicate; semantic limit-head validity
is deliberately not part of parsing. -/
def positiveExprDecode : Nat → Option FixedLimitPositiveExpr
  | n =>
    if h0 : n%4=0 then some (.constant (n/4))
    else if h1 : n%4=1 then if n=1 then some .input else none
    else
      have hn : 0<n := by omega
      have hdiv : n/4<n := Nat.div_lt_self hn (by decide)
      let p := (n/4).unpair
      have hleft : p.1<n := (Nat.unpair_left_le _).trans_lt hdiv
      have hright : p.2<n := (Nat.unpair_right_le _).trans_lt hdiv
      if h2 : n%4=2 then
        (positiveExprDecode p.1).bind fun E =>
          (positiveExprDecode p.2).map fun F => .add E F
      else
        if hh : rawNormalCode p.1=1 then
          let rho : NONote := ⟨rawNoteDecode p.1,(rawNormalDecodeCorrect p.1).mp hh⟩
          (positiveExprDecode p.2).map fun E => .head rho E
        else none
  termination_by n => n
  decreasing_by all_goals assumption

end LogicLineages.OrdinalComparison
