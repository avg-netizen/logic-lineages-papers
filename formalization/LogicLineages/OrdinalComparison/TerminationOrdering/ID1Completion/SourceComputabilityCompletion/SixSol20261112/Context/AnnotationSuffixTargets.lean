module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalIndexedPrefixCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalAdditionLawsProof (add)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalIndexedPrefixCasesTargets (bump)
/-- The SAME original annotation scan splits at a genuine raw prefix past the
actual parent arity. The suffix is the actual inherited term-job map, in its
literal order. Every hypothesis is an original arithmetic Program graph; no
annotation coherence, map law, covariance or result invariant is supplied. -/
def ActualInheritedScanSplit : Prop := ∀ (arity : Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (offset typ raw front suffix jobs prefix count full mapped : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (bump arity offset) front)) →
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)) →
  Nonempty (Derivation body Delta
    (graph5 OriginalHereditaryAnnotatedExpansion.scan prefix (bump arity offset) z typ raw jobs)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count suffix)) →
  Nonempty (Derivation body Delta
    (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add (bump arity offset) count) z typ raw jobs)) →
  Nonempty (Derivation body Delta
    (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) mapped suffix typ)) →
  Nonempty (Derivation body Delta
    (graph2 InternalApplicationValidityStackAppend.append full prefix mapped))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixTargets
