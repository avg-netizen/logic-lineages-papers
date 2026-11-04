module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecTargets
open Source NumberedRewriteReduction NumberedMultisetCertificate

/-- The original occurrence-indexed replacement test on all ordered lists and witnesses. -/
def ActualReplacementTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
        List (Packed (Fin n) arity Gamma) × List MarkWitness =>
      replacementTest p.1 p.2.1 p.2.2)

/-- The original multiset certificate decision with every certificate field retained. -/
def ActualMultisetTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
        List (Packed (Fin n) arity Gamma) × MultisetCertificate n arity Gamma =>
      multisetTest p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecTargets
