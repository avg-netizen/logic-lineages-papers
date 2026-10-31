module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment
open SyntaxCode OrdinalSyntax

/-- Literal variable and constant clauses. Coordinate zero of a recursor is
exactly the source numeral two, not an evaluated or reassociated ordinal. -/
def primeCode (tag payload resultLevel : Nat) : List Nat :=
  if tag=0 then (List.range (resultLevel+1)).map (fun i => 8*Nat.pair payload i+3)
  else if tag=4 then (List.range (resultLevel+1)).map (fun i =>
    if i=0 then repeatCode 2 1 else if i=typeLevel payload+2 then 2 else 1)
  else List.replicate (resultLevel+1) 1

/-- Actual raw original-T compiler for the declared default association policy.
The context is external; it is extended only at a literal lambda. Source
checking and backend partial failures are explicit Option failures. -/
def assignmentCode (Γ : List Nat) : Nat → Option (List Nat)
  | n => do
    let resultType ← check Γ n
    if n%8<5 then pure (primeCode (n%8) (n/8) (typeLevel resultType))
    else if h : n%8=5 ∨ n%8=6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then do
        let argType ← check Γ p.2
        let f ← assignmentCode Γ p.1
        let a ← assignmentCode Γ p.2
        pure (defaultApplicationCode (typeLevel resultType) (typeLevel argType) f a)
      else do
        let bodyType ← check (p.1::Γ) p.2
        let b ← assignmentCode (p.1::Γ) p.2
        abstractionCode (typeLevel p.1) (typeLevel bodyType) b
    else none
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment
