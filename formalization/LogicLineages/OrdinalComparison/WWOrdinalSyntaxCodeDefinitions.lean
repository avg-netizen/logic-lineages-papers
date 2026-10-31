module
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Literal ordinal AST encoding; variables retain their supplied full code.
Tags 0/1/2 are zero/one/omega, 3 variable, 4/5/6 add/emul/collapse. -/
def code {ι : Type} (index : ι → Nat) : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Nat
  | .zero => 0
  | .one => 1
  | .omega => 2
  | .var x => 8 * index x + 3
  | .add a b => 8 * Nat.pair (code index a) (code index b) + 4
  | .emul a b => 8 * Nat.pair (code index a) (code index b) + 5
  | .collapse a b => 8 * Nat.pair (code index a) (code index b) + 6

/-- Both de Bruijn position and ordinal component survive erasure. -/
def componentCode {Γ : List Ty} (c : OrdinalComponent Γ) : Nat :=
  Nat.pair (SourceTypedPorts.variableIndex c.2.1) c.2.2.val

def typedCode {Γ : List Ty} (t : OrdinalExpression Γ) : Nat := code componentCode t

/-- Total numerical fold. Malformed atomic payloads/tags are sent to leaf;
no normalization, semantic equality test, or variable identification occurs. -/
def fold {α : Type} (leaf : Nat → α) (branch : Nat → α → α → α) : Nat → α
  | n => if h : n % 8 < 4 ∨ n % 8 = 7 then leaf n else
    have hn : 0 < n := by omega
    have hd : n / 8 < n := Nat.div_lt_self hn (by decide)
    let p := (n / 8).unpair
    have hl : p.1 < n := (Nat.unpair_left_le _).trans_lt hd
    have hr : p.2 < n := (Nat.unpair_right_le _).trans_lt hd
    branch (n % 8) (fold leaf branch p.1) (fold leaf branch p.2)
termination_by n => n
decreasing_by all_goals assumption

/-- Independent structural fold on the original ordinal expression. -/
def termFold {ι α : Type} (index : ι → Nat) (leaf : Nat → α)
    (branch : Nat → α → α → α) : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → α
  | .zero => leaf 0
  | .one => leaf 1
  | .omega => leaf 2
  | .var x => leaf (8 * index x + 3)
  | .add a b => branch 4 (termFold index leaf branch a) (termFold index leaf branch b)
  | .emul a b => branch 5 (termFold index leaf branch a) (termFold index leaf branch b)
  | .collapse a b => branch 6 (termFold index leaf branch a) (termFold index leaf branch b)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
