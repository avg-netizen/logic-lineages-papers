module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields {alpha : Type} (p : Program 3)
    (raw a b i j upper lower left right : OTerm alpha) : Formula alpha :=
  InternalLessThan.strictLess i (suc j) ⊓
    (graph3 p upper b (suc j) raw ⊓
      (graph3 p left a i upper ⊓
        (graph3 p lower a i raw ⊓ graph3 p right b j lower)))

/-- All eight deletion parameters/results remain bound inside the raw IH. -/
def commutationMatrix {alpha : Type} (p : Program 3) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  (fields p (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
    (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))
    (.var (.inr 6)) (.var (.inr 7))).imp
      (equal (.var (.inr 6)) (.var (.inr 7)))

def AtRaw {alpha : Type} (p : Program 3) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (commutationMatrix p raw)

def rawPredicate {alpha : Type} (p : Program 3) : Formula (alpha ⊕ Fin 1) :=
  AtRaw p (.var (.inr 0))

def BelowRaw {alpha : Type} (p : Program 3) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate p) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalDefinitions
