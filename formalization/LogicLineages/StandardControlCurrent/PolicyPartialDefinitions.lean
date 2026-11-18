module
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartial
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

def mergeCoordinate (p : Policy) (tag a b : Nat) : Option Nat := do
  let x ← if tag=5 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [a,a]
    else some a
  PolicyShape.macroCode p (PolicyShape.siteCode (if tag=5 then .activeExp else .activeAdd)) 2 [x,b,1]

def mergeCode (p : Policy) (level tag : Nat) (a b : List Nat) : Option (List Nat) :=
  (List.range (level+2)).foldl (fun acc j => do
    let xs ← acc
    let x ← mergeCoordinate p tag (a.getD j 0) (b.getD j 0)
    pure (xs ++ [x])) (some [])

/-- Actual raw-code policy partial: whole-head-free test has precedence, and
recursive grade changes are exactly those of AdmissiblePartial.run. -/
def run (p : Policy) : Nat → Nat → Nat → Option (List Nat)
  | level, i, n =>
    if headFree n then some (partialFree level i n)
    else if n%8=3 then if i=(n/8).unpair.2 then some (List.replicate (level+2) 1) else none
    else if h : n%8=4 ∨ n%8=5 ∨ n%8=6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let q := (n/8).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=4 then do
        let a ← run p level i q.1
        let b ← run p level i q.2
        mergeCode p level 4 a b
      else if n%8=5 then
        if 0 < i then do
          let a ← run p level (i+1) q.1
          let b ← run p level i q.2
          mergeCode p level 5 a b
        else none
      else if i=0 then do
        let a ← run p level 1 q.1
        let b ← run p level 0 q.2
        pure (partialCollapse level q.1 a b)
      else none
    else none
termination_by _ _ n => n
decreasing_by all_goals assumption
end LogicLineages.StandardControlCurrent.PolicyPartial
