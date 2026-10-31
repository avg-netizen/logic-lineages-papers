module
public import LogicLineages.OrdinalComparison.WWGroundClosingDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundClosingCode
open SyntaxCode

/-- Erased capture-avoiding ground closing: retain exactly the first `depth`
indices, and replace every other variable by literal zero. Binder domains and
all polymorphic constant types are retained, including internal types. -/
def closeRaw (depth : Nat) : Raw → Raw
  | .var i => if i < depth then .var i else .zero
  | .zero => .zero
  | .succ => .succ
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .app f a => .app (closeRaw depth f) (closeRaw depth a)
  | .lam σ b => .lam σ (closeRaw (depth+1) b)

/-- Total numeric source-code closing in the original radix-eight codec.
Malformed atomic tags (7, or noncanonical zero/successor payloads) are replaced
locally by literal zero code 1. Composite nodes recursively use that convention.
No typed parser, choice function, or evaluation of the source term is used. -/
def closeCode (depth : Nat) : Nat → Nat
  | n =>
    if n%8=0 then if n/8 < depth then n else 1
    else if n%8=1 then 1
    else if n%8=2 then if n/8=0 then 2 else 1
    else if n%8=3 then n
    else if n%8=4 then n
    else if h : n%8=5 ∨ n%8=6 then
      have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then 8*Nat.pair (closeCode depth p.1) (closeCode depth p.2)+5
      else 8*Nat.pair p.1 (closeCode (depth+1) p.2)+6
    else 1
termination_by n => n
decreasing_by all_goals assumption

/-- A typed map implements this exact index-based closing. This property is
used only to state the general binder induction, not as an effectiveness premise. -/
def Compatible {Γ Δ : List Ty} (depth : Nat) (r : GroundClosing.GroundMap Γ Δ) : Prop :=
  ∀ {σ} (x : Variable Γ σ), erase (r x).source = closeRaw depth (.var (SourceTypedPorts.variableIndex x))
end LogicLineages.OrdinalComparison.Source.GroundClosingCode
