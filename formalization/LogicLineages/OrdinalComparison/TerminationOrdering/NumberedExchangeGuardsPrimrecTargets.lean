module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeAssemblyPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedEnumerationOperationsPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

def ActualHeadEquivalencePrimitive : Prop :=
  ∀ n : Nat, Primrec (fun p : HeadCode (Fin n) × HeadCode (Fin n) =>
    decide (RecursiveComparison.headEquivalent (decodeHead p.1) (decodeHead p.2)))

def ActualPermutationPrimitive : Prop :=
  ∀ n : Nat, Primrec (fun p : List (Ty × Code (Fin n)) × List (Ty × Code (Fin n)) =>
    decide (p.1.Perm p.2))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecTargets
