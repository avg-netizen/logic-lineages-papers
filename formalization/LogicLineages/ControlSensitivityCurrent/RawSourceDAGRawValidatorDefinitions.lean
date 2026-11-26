module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
open LogicLineages.OrdinalComparison.Source
abbrev RawSpec := List Nat × Nat
/-- Bounds are checked separately: a default element never legitimizes an invalid index. -/
def lookup (ss : List RawSpec) (s : RawSpec) (i : Nat) : Bool :=
  decide (i < ss.length) && decide (ss.getD i ([],0) = s)
def «variable» (Γ : List Nat) (t i : Nat) : Bool :=
  decide (i < Γ.length) && decide (Γ.getD i 0 = t)
/-- Literal seven-constructor checker; neither type decoding nor a semantic oracle occurs here. -/
def nodeValid (Γ : List Nat) (a : Node) (ss : List RawSpec) : Bool :=
  let Δ := a.1
  let t := a.2.1
  let args := a.2.2.2
  let x := args.getD 0 0
  let y := args.getD 1 0
  let z := args.getD 2 0
  let tag := a.2.2.1
  if tag = 0 then decide (args.length = 1) && «variable» (Δ++Γ) t x
  else if tag = 1 then decide (args.length = 3) &&
    lookup ss (Δ,SyntaxCode.arrowCode x t) y && lookup ss (Δ,x) z
  else if tag = 2 then decide (args.length = 3) &&
    decide (t = SyntaxCode.arrowCode x y) && lookup ss (x::Δ,y) z
  else if tag = 3 then decide (args.length = 0) && decide (t = 0)
  else if tag = 4 then decide (args.length = 0) && decide (t = SyntaxCode.arrowCode 0 0)
  else if tag = 5 then decide (args.length = 1) && decide (t = SyntaxCode.caseCode x)
  else if tag = 6 then decide (args.length = 1) && decide (t = SyntaxCode.recCode x)
  else false
/-- Tail-first fold preserves the literal newest-first table and accumulated validity. -/
def scan (Γ : List Nat) (a : Node) (state : List RawSpec × Bool) : List RawSpec × Bool :=
  ((a.1,a.2.1)::state.1,state.2 && nodeValid Γ a state.1)
def graph (Γ : List Nat) (as : List Node) : List RawSpec × Bool :=
  as.foldr (scan Γ) ([],true)
def check (c : Code) : Bool :=
  let s := graph c.1 c.2.1
  s.2 && lookup s.1 ([],c.2.2.2) c.2.2.1
/-- A computable candidate for the proved literal decode/encode reifier, not a replacement decoder. -/
def reify (c : Code) : Option Code := if check c then some c else none
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.RawValidator
