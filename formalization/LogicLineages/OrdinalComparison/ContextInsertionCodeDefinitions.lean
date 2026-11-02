module
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ContextInsertionCode

/-- Insert Δ below exactly Θ; all existing typed names retain their identity. -/
def insertion (Θ Δ Γ : List Ty) : Renaming (Θ++Γ) (Θ++(Δ++Γ)) :=
  HeterogeneousUnaryAssembly.prefixLift (SourceTypedPorts.shiftVariable Δ) Θ

def indexCode (depth count i : Nat) : Nat := if i<depth then i else i+count

def sourceCode (depth count : Nat) : Nat → Nat
  | n =>
    if n%8=0 then 8*indexCode depth count (n/8)
    else if n%8=1 then 1
    else if n%8=2 then if n/8=0 then 2 else 1
    else if n%8=3 then n
    else if n%8=4 then n
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then 8*Nat.pair (sourceCode depth count p.1) (sourceCode depth count p.2)+5
      else 8*Nat.pair p.1 (sourceCode (depth+1) count p.2)+6
    else 1
termination_by n => n
decreasing_by all_goals assumption

def ordinalLeaf (depth count n : Nat) : Nat :=
  if n%8=3 then
    let p := (n/8).unpair
    8*Nat.pair (indexCode depth count p.1) p.2+3
  else n

def ordinalCode (depth count n : Nat) : Nat :=
  OrdinalSyntax.fold (ordinalLeaf depth count) (fun tag a b => 8*Nat.pair a b+tag) n

def vectorCode (depth count : Nat) (v : List Nat) : List Nat := v.map (ordinalCode depth count)
end LogicLineages.OrdinalComparison.Source.ContextInsertionCode
