module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
/-- Induction is on actual parent context length. All constructor endpoints,
parameters and payloads are internally quantified, so deletion may change them.
No parent SameEvaluator is in either antecedent. -/
def applicationFields {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 16 → OTerm alpha) : Formula alpha :=
 graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) (xs 0) (xs 13) ⊓
 (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) (xs 1) (xs 13) ⊓
 (InternalApplicationValidityClosure.applicationConstructors (xs 6) (xs 7) (xs 8) (xs 9) (xs 11) (xs 2) (xs 4) (xs 0) ⊓
 (InternalApplicationValidityClosure.applicationConstructors (xs 6) (xs 7) (xs 8) (xs 10) (xs 12) (xs 3) (xs 5) (xs 1) ⊓
 (AdmittedPair R H G M W (xs 2) (xs 3) (xs 13) ⊓
 (AdmittedPair R H G M W (xs 4) (xs 5) (xs 13) ⊓
 (graph2 InternalPairing.pairing (xs 13) (xs 14) (xs 15) ⊓
 OriginalContextInsertion.lengthGraph count (xs 15)))))))
def lambdaFields {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula alpha :=
 graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) (xs 0) (xs 6) ⊓
 (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) (xs 1) (xs 6) ⊓
 (graph2 InternalPairing.pairing (xs 6) (xs 8) (xs 9) ⊓
 (graph2 InternalListCodec.consCode (xs 10) (xs 4) (xs 9) ⊓
 (graph2 InternalPairing.pairing (xs 7) (xs 8) (xs 10) ⊓
 (graph3 OriginalLambdaConstructor.constructor (xs 0) (xs 4) (xs 5) (xs 2) ⊓
 (graph3 OriginalLambdaConstructor.constructor (xs 1) (xs 4) (xs 5) (xs 3) ⊓
 (graph1 InternalUnpair.left (xs 5) (xs 2) ⊓
 (graph1 InternalUnpair.left (xs 5) (xs 3) ⊓
 (AdmittedPair R H G M W (xs 2) (xs 3) (xs 7) ⊓
 OriginalContextInsertion.lengthGraph count (xs 9))))))))))
def applicationMatrix {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) : Formula (alpha ⊕ Fin 16) :=
 (applicationFields R H G M W (count.relabel Sum.inl) (fun i => .var (.inr i))).imp
 (AdmittedPair R H G M W (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 13)))
def lambdaMatrix {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) : Formula (alpha ⊕ Fin 11) :=
 (lambdaFields R H G M W (count.relabel Sum.inl) (fun i => .var (.inr i))).imp
 (AdmittedPair R H G M W (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 6)))
def AtLength {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (applicationMatrix R H G M W count) ⊓
 InternalClosedPrograms.allBlock (lambdaMatrix R H G M W count)
def predicate {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2) : Formula (alpha ⊕ Fin 1) :=
 AtLength R H G M W (.var (.inr 0))
def BelowLength {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (predicate R H G M W) count
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionDefinitions
