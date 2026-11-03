module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecTargets
open Source NumberedRewriteReduction NumberedAuxiliaryEnumeration NumberedAuxiliaryDecoding

def ActualClassCodesPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      classCodes p.1.1 p.1.2 p.2)

def ActualClassCandidatesPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      classCandidates p.1.1 p.1.2 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecTargets
