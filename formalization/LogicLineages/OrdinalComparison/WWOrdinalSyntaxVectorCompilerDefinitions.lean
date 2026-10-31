module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
public import LogicLineages.OrdinalComparison.WWQuerySyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open ForwardTranslation

def collectAtoms : List (Option Nat) → Option (List Nat)
  | [] => some []
  | a::rest => do
    let x ← a
    let xs ← collectAtoms rest
    pure (x::xs)

/-- Refuse an empty vector or any failed scalar/positive syntax extraction.
Output carries only literal AST codes, never pre-normalized ordinal heads. -/
def compileVectorCode : List Nat → Option EncodedVector
  | [] => none
  | a::rest => do
    let s ← (extraction a).2
    let p ← collectAtoms (rest.map (fun n => (extraction n).1))
    pure (s,p)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
