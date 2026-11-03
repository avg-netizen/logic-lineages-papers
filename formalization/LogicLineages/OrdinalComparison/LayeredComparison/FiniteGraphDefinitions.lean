module
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph
/-- Expand ALL finite child occurrences, preserving repetitions and order. -/
def frontier {A:Type} (children:A→List A) (a:A) (n:Nat):List A:=
  ((fun xs:List A=>xs.flatMap children)^[n]) [a]
/-- Literal bottom-up finite evaluation graph. The next frontier is computed
from the original input and remaining natural depth. -/
def graph {A B:Type} [DecidableEq A] (children:A→List A) (assemble:A→List B→B)
    (μ:A→Nat) (a:A):Nat→List (A×B)
  | 0=>[]
  | n+1=>(frontier children a (μ a-n)).map (fun b=>
      (b,assemble b ((children b).filterMap (fun c=>(graph children assemble μ a n).lookup c))))
end LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph
