module
public import LogicLineages.StandardControlCurrent.PolicyConstructorsDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAbstractionDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignment
open OrdinalComparison Source Source.AdmissibleSum Source.SyntaxCode Source.OrdinalSyntax

def primeCode (p : Policy) (tag payload resultLevel : Nat) : Option (List Nat) :=
  if tag=0 then some ((List.range (resultLevel+1)).map (fun i => 8*Nat.pair payload i+3))
  else if tag=4 then PolicyConstructors.recursorCode p (typeLevel payload) resultLevel
  else some (List.replicate (resultLevel+1) 1)

/-- Literal original typed-source compiler with external raw context. Every
source-check and backend failure is explicit; no normalization takes place. -/
def assignmentCode (p : Policy) (Γ : List Nat) : Nat → Option (List Nat)
  | n => do
    let resultType ← check Γ n
    if n%8<5 then primeCode p (n%8) (n/8) (typeLevel resultType)
    else if h : n%8=5 ∨ n%8=6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let q := (n/8).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then do
        let argType ← check Γ q.2
        let f ← assignmentCode p Γ q.1
        let a ← assignmentCode p Γ q.2
        PolicyConstructors.applicationCode p (typeLevel resultType) (typeLevel argType) f a
      else do
        let bodyType ← check (q.1::Γ) q.2
        let b ← assignmentCode p (q.1::Γ) q.2
        PolicyAbstraction.abstractionCode p (typeLevel q.1) (typeLevel bodyType) b
    else none
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.StandardControlCurrent.PolicyAssignment
