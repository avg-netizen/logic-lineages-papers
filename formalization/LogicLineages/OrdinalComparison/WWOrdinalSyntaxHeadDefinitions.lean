module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

def headLeafFree (n : Nat) : Bool :=
  if n%8=3 then decide ((n/8).unpair.1 ≠ 0) else true

def headFree (n : Nat) : Bool := fold headLeafFree (fun _ a b => a && b) n

def headLeafClosure (n : Nat) : Nat :=
  if n%8=3 then
    if (n/8).unpair.1=0 then 1
    else 8 * Nat.pair ((n/8).unpair.1-1) (n/8).unpair.2 + 3
  else n

def headClosure (n : Nat) : Nat :=
  fold headLeafClosure (fun tag a b => 8 * Nat.pair a b + tag) n

/-- Simultaneously computes whole-head-freeness and its priority-sensitive
partial size. Actual subtrees are never eliminated by their semantic value. -/
def headSizeData (n : Nat) : Bool × Nat :=
  fold (fun k => (headLeafFree k, 1))
    (fun tag a b => (a.1 && b.1,
      if a.1 && b.1 then 1 else (if tag=5 then 2*a.2 else a.2) + b.2 + 1)) n

def partialSize (n : Nat) : Nat := (headSizeData n).2
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
