module
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeDefinitions
public import LogicLineages.OrdinalComparison.WWUnaryCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode
open SyntaxCode

/-- fresh=true keeps the tracked slot and inserts a fresh unused old slot;
fresh=false deletes exactly one ground slot by literal source zero. -/
def variableRaw (fresh : Bool) (depth i : Nat) : Raw :=
  if i < depth then .var i else
  if fresh then (if i = depth then .var i else .var (i+1))
  else if i = depth then .zero else .var (i-1)

def mapRaw (fresh : Bool) (depth : Nat) : Raw → Raw
  | .var i => variableRaw fresh depth i
  | .zero => .zero
  | .succ => .succ
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .app f a => .app (mapRaw fresh depth f) (mapRaw fresh depth a)
  | .lam σ b => .lam σ (mapRaw fresh (depth+1) b)

def variableCode (fresh : Bool) (depth i : Nat) : Nat :=
  if i < depth then 8*i else
  if fresh then (if i = depth then 8*i else 8*(i+1))
  else if i = depth then 1 else 8*(i-1)

/-- Numeric constructor transcription. Malformed zero/successor payloads and
unused tag7 totalize to source zero; no validity claim on malformed codes. -/
def mapCode (fresh : Bool) (depth : Nat) : Nat → Nat
  | n =>
    if n%8=0 then variableCode fresh depth (n/8)
    else if n%8=1 then 1
    else if n%8=2 then if n/8=0 then 2 else 1
    else if n%8=3 then n
    else if n%8=4 then n
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then 8*Nat.pair (mapCode fresh depth p.1) (mapCode fresh depth p.2)+5
      else 8*Nat.pair p.1 (mapCode fresh (depth+1) p.2)+6
    else 1
termination_by n => n
decreasing_by all_goals assumption

/-- General typed substitution calibration, discharged at each concrete map. -/
def Compatible {Γ Δ : List Ty} (fresh : Bool) (depth : Nat) (r : GroundClosing.GroundMap Γ Δ) : Prop :=
  ∀ {σ} (x : Variable Γ σ), erase (r x).source = variableRaw fresh depth (SourceTypedPorts.variableIndex x)
end LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode
