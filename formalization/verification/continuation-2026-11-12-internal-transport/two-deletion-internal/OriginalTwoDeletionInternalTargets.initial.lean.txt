module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
/-- Independent arithmetic graph identity on all raw inputs, including
malformed leaves. The later original cutoff is suc j; after the earlier
deletion it is j. Erased types are literal arbitrary arithmetic inputs.
No native evaluation, source-typing or desired-output equality premise. -/
def RawCommutation : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw a b i j upper lower left right : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((InternalLessThan.strictLess i (InternalTagArithmeticSyntaxProof.suc j) ⊓
      (graph3 eraseRaw upper b (InternalTagArithmeticSyntaxProof.suc j) raw ⊓
       (graph3 eraseRaw left a i upper ⊓
        (graph3 eraseRaw lower a i raw ⊓ graph3 eraseRaw right b j lower)))).imp
      (equal left right)))
/-- The identical identity at the literal packed wrapper. The packed type
coordinate is retained; no decoded-context or canonical representative claim. -/
def PackedCommutation : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw a b i j upper lower left right : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((InternalLessThan.strictLess i (InternalTagArithmeticSyntaxProof.suc j) ⊓
      (graph3 erasePackedRaw upper b (InternalTagArithmeticSyntaxProof.suc j) raw ⊓
       (graph3 erasePackedRaw left a i upper ⊓
        (graph3 erasePackedRaw lower a i raw ⊓ graph3 erasePackedRaw right b j lower)))).imp
      (equal left right)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTargets
