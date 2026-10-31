module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode

/-- Minimal erased T syntax. Context is external; only the abstraction domain
and polymorphic constant type are written in syntax, as numerical type codes. -/
inductive Raw where
  | var (index : Nat)
  | zero | succ
  | caseC (type : Nat) | recC (type : Nat)
  | app (fn arg : Raw)
  | lam (domain : Nat) (body : Raw)
  deriving DecidableEq

def code : Raw → Nat
  | .var i => 8*i
  | .zero => 1
  | .succ => 2
  | .caseC τ => 8*τ+3
  | .recC τ => 8*τ+4
  | .app f a => 8*Nat.pair (code f) (code a)+5
  | .lam σ b => 8*Nat.pair σ (code b)+6

def erase {Γ : List Ty} {τ : Ty} : OriginalTerm Γ τ → Raw
  | .var v => .var (SourceTypedPorts.variableIndex v)
  | .zeroC => .zero
  | .succC => .succ
  | .caseC σ => .caseC (typeCode σ)
  | .recC σ => .recC (typeCode σ)
  | .app f a => .app (erase f) (erase a)
  | @Term.lam _ _ _ σ _ b => .lam (typeCode σ) (erase b)
  | .ranked s _ => nomatch s

def encodeTerm {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) : Nat := code (erase t)

/-- Partial parser. Noncanonical zero/succ payloads and tag 7 are rejected. -/
def decode : Nat → Option Raw
  | n =>
    if n % 8 = 0 then some (.var (n/8))
    else if n % 8 = 1 then if n/8=0 then some .zero else none
    else if n % 8 = 2 then if n/8=0 then some .succ else none
    else if n % 8 = 3 then some (.caseC (n/8))
    else if n % 8 = 4 then some (.recC (n/8))
    else if h : n % 8 = 5 ∨ n % 8 = 6 then
      have hn : 0<n := by omega
      have hd : n/8<n := Nat.div_lt_self hn (by decide)
      let p := (n/8).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%8=5 then do
        let f ← decode p.1
        let a ← decode p.2
        pure (.app f a)
      else (decode p.2).map (.lam p.1)
    else none
termination_by n => n
decreasing_by all_goals assumption
end LogicLineages.OrdinalComparison.Source.SyntaxCode
