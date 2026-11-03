module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadCollectedRow
open CommonHeadLargeRow

def keys (row : Row) : List Nat := (row.map Prod.snd).dedup

def coefficient (row : Row) (t : Nat) : Int :=
  (row.map (fun a => if a.2=t then a.1 else 0)).sum

/-- Literal equal-input blocks; cancellation removes the whole zero block. -/
def collect (row : Row) : Row :=
  ((keys row).map (fun t => (coefficient row t,t))).filter (fun a => a.1 != 0)

def weighted (f : Nat → Int) (row : Row) : Int :=
  (row.map (fun a => a.1*f a.2)).sum
end LogicLineages.OrdinalComparison.CommonHeadCollectedRow
