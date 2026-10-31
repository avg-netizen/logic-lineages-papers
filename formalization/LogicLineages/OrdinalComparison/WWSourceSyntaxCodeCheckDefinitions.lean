module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode

def appResult (f a : Option Nat) : Option Nat := do
  let tf ← f
  let ta ← a
  if tf=0 then none else
    let p := (tf-1).unpair
    if p.1=ta then some p.2 else none

def inferRaw (Γ : List Nat) : Raw → Option Nat
  | .var i => Γ[i]?
  | .zero => some 0
  | .succ => some (arrowCode 0 0)
  | .caseC τ => some (caseCode τ)
  | .recC τ => some (recCode τ)
  | .app f a => appResult (inferRaw Γ f) (inferRaw Γ a)
  | .lam σ b => (inferRaw (σ::Γ) b).map (arrowCode σ)

/-- Actual context-sensitive numerical checker. Context is passed once, and
only the binder extends it. Recursive child syntax codes strictly decrease. -/
def check (Γ : List Nat) : Nat → Option Nat
  | n =>
    if n%8=0 then Γ[n/8]?
    else if n%8=1 then if n/8=0 then some 0 else none
    else if n%8=2 then if n/8=0 then some (arrowCode 0 0) else none
    else if n%8=3 then some (caseCode (n/8))
    else if n%8=4 then some (recCode (n/8))
    else if h : n%8=5 ∨ n%8=6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then appResult (check Γ p.1) (check Γ p.2)
      else (check (p.1::Γ) p.2).map (arrowCode p.1)
    else none
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.SyntaxCode
