module
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList
open HeterogeneousUnaryAssembly ScalarCarrierAccounting
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def scale (b : Nat) : Nat := 2^b

def paidList {Γ : List Ty} (b : Nat) (xs : List (Operator Γ)) (caller : Operator Γ) : List (Operator Γ) :=
  (List.replicate (scale b) xs).flatten ++ List.replicate (scale b) caller

noncomputable def sourceSum {Γ : List Ty} (xs : List (Operator Γ)) : Ordinal :=
  (xs.map (fun op => unitValue (op.vector 1))).foldr ordinalNaturalSum 0

def gap {Γ : List Ty} (b : Nat) (xs : List (Operator Γ)) (c : Nat) : Nat :=
  scale b * (c - 3*xs.length - 3) - 1

def unaryInput (Γ : List Ty) (t : OriginalTerm Γ (Ty.curriedGround 1)) (v : OrdinalVector Γ 1)
    (hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v) : Operator Γ :=
  ⟨[],t,v,hv⟩
end LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList
