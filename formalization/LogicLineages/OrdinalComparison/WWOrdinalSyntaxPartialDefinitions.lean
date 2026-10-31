module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

/-- An explicit effective admissible convention: all seven macro sites use
ordered left combs. This is not claimed to be the manuscript's distinct
printed default (whose optional box tail is right associated). -/
def leftShape : (n : Nat) → AdmissibleSum.Shape (n+1)
  | 0 => .leaf
  | n+1 => .join (leftShape n) .leaf

def allLeftPolicy : AdmissibleSum.Policy := ⟨fun _ n => leftShape n⟩

def node (tag a b : Nat) : Nat := 8 * Nat.pair a b + tag

def partialFree (level i n : Nat) : List Nat :=
  (List.range (level+2)).map (fun j => if i=j then node 4 (headClosure n) 1 else 1)

def partialMerge (level tag : Nat) (a b : List Nat) : List Nat :=
  (List.range (level+2)).map (fun j =>
    node 4 (node 4 (if tag=5 then node 4 (a.getD j 0) (a.getD j 0) else a.getD j 0)
      (b.getD j 0)) 1)

def partialCollapse (level head : Nat) (a b : List Nat) : List Nat :=
  (List.range (level+2)).map (fun j => if j=0 then node 6 (headClosure head) (b.getD 0 0)
    else node 4 (a.getD j 0) (b.getD j 0))

/-- Literal all-left partial compiler. Whole-free test comes before all
constructor and grade tests; no semantic simplification is used. -/
def partialRun : Nat → Nat → Nat → Option (List Nat)
  | level, i, n =>
    if headFree n then some (partialFree level i n)
    else if n%8=3 then if i=(n/8).unpair.2 then some (List.replicate (level+2) 1) else none
    else if h : n%8=4 ∨ n%8=5 ∨ n%8=6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=4 then do
        let a ← partialRun level i p.1
        let b ← partialRun level i p.2
        pure (partialMerge level 4 a b)
      else if n % 8 = 5 then
        if 0 < i then do
          let a ← partialRun level (i+1) p.1
          let b ← partialRun level i p.2
          pure (partialMerge level 5 a b)
        else none
      else
        if i = 0 then do
          let a ← partialRun level 1 p.1
          let b ← partialRun level 0 p.2
          pure (partialCollapse level p.1 a b)
        else none
    else none
termination_by _ _ n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
