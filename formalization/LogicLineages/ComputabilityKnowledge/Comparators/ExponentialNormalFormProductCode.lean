module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCode

@[expose] public section

/-! Full exact code implementation of N2. The actual existing mathematical
exponentialProduct is the reference, on every raw natural input. Genuine
uniform primitive recursion is a separate required conclusion.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProductCode

open ExponentialHereditaryCodec ExponentialNormalFormProduct
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCode

def SourceImplementation : Prop :=
  ∀ (d h a b : Nat),
    CodeCanonical d (h + 1) (exponentialProductCode d h a b) ∧
    formDecode d (h + 1) (exponentialProductCode d h a b) =
      exponentialProduct h (formDecode d h a) (formDecode d h b)

def ActualPrimitiveRecursion : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    exponentialProductCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := SourceImplementation ∧ ActualPrimitiveRecursion

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProductCode
