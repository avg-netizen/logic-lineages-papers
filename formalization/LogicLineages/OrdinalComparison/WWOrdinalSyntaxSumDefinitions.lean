module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

def sumPrefix : Nat → List Nat → Nat
  | 0, xs => xs.getD 0 0
  | n+1, xs => node 4 (sumPrefix n xs) (xs.getD (n+1) 0)

def repeatCode (count t : Nat) : Nat :=
  if count=0 then 0 else sumPrefix (count-1) (List.replicate count t)

def vectorCode {Γ : List Ty} {m : Nat} (v : OrdinalVector Γ m) : List Nat :=
  List.ofFn (fun j => typedCode (v j))
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
