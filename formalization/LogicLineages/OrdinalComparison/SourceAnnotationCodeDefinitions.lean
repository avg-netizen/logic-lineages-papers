module
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderDefinitions
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode
open ScalarAnnotationData

def operatorCode {Γ} (op : Operator Γ) : Nat :=
  Nat.pair op.arity (Nat.pair (SyntaxCode.encodeTerm op.source) (Encodable.encode (OrdinalSyntax.vectorCode op.vector)))
def operatorArity (n : Nat) : Nat := n.unpair.1
def operatorSource (n : Nat) : Nat := n.unpair.2.unpair.1
def operatorVector (n : Nat) : List Nat :=
  (Encodable.decode (α := List Nat) n.unpair.2.unpair.2).getD []
def operatorHead (n : Nat) : Nat := (operatorVector n).getD 1 0

def code {k Γ F} : Tree k Γ F → Nat
  | .free q => 4 * OrdinalSyntax.typedCode q
  | .tracked => 1
  | .add a b => 4 * Nat.pair (code a) (code b) + 2
  | .collapse op tail => 4 * Nat.pair (operatorCode op) (code tail) + 3

/-- Operator payload is data, never recursively traversed as a scalar tree. -/
def fold (atom : Nat → Nat → Nat → Nat) (add collapse : Nat → Nat → Nat → Nat)
    (ctx : Nat) : Nat → Nat
  | n =>
    if h : n%4<2 then atom ctx (n%4) (n/4) else
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let p := (n/4).unpair
      have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then add ctx (fold atom add collapse ctx p.1) (fold atom add collapse ctx p.2)
      else collapse ctx p.1 (fold atom add collapse ctx p.2)
termination_by n => n
decreasing_by all_goals assumption

def eraseCode (trackedIndex n : Nat) : Nat :=
  fold (fun i tag payload => if tag=0 then payload else 8*Nat.pair i 0+3)
    (fun _ a b => 8*Nat.pair a b+4) (fun _ op tail => 8*Nat.pair (operatorHead op) tail+6) trackedIndex n

def repeatTail (d : Nat) : Nat → Nat
  | 0 => d
  | n+1 => 4*Nat.pair (repeatTail d n) d+2

def repeatCode (count d : Nat) : Nat := match count with
  | 0 => 0
  | n+1 => repeatTail d n

def closeOperatorCode (n : Nat) : Nat := Nat.pair (operatorArity n)
  (Nat.pair (SourceCarrierMapCode.mapCode false 0 (operatorSource n))
    (Encodable.encode ((operatorVector n).map OrdinalSyntax.headClosure)))

def closeCode (n : Nat) : Nat :=
  fold (fun _ tag payload => if tag=0 then 4*OrdinalSyntax.headClosure payload else 1)
    (fun _ a b => 4*Nat.pair a b+2)
    (fun _ op tail => 4*Nat.pair (closeOperatorCode op) tail+3) 0 n
end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode
