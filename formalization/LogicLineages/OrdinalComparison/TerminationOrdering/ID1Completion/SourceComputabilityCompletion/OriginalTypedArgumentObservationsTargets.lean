module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalTypedArgumentObservations
/-- Arbitrary actual R, every typed original argument list, unchanged runtime
parameter. No assumption that R computes a canonical representative. -/
def NativeCalibration : Prop := ∀ (R : Program 2) (n : Nat) (arity : Fin n → Nat)
 (Gamma types : List Ty) (args : AuxArguments (Fin n) arity Gamma types) (parameter : Nat),
 evaluate (argumentObservations R) (ofFn ![codeNumber (argumentsCode args),parameter]) =
 numbersNumber ((argumentList args).map (fun q =>
   Nat.pair (typeNumber q.1) (evaluate R (ofFn ![packedNumber q,parameter]))))
/-- Separate numeric-reversal calibration, all numeric lists and duplicates. -/
def NativeReverse : Prop := ∀ xs : List Nat,
 evaluate reverse (numbersNumber xs ::ᵥ nil) = numbersNumber xs.reverse
/-- Literal original tag6 nil. -/
def InternalNil : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (raw parameter out : OTerm alpha),
 Nonempty (Derivation body [] ((programGraph OriginalRawSyntaxTransport.nilConstructor raw Fin.elim0).imp
 ((graph2 (argumentObservations R) out raw parameter).iff (equal out OrdinaryArithmetic.zeroTerm))))
/-- Literal original tag7 cons and actual typed child observation. The tail
observer uses exactly the same parameter. No native-reflection premise. -/
def InternalCons : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type)
 (raw typ child tail packed observation typedObservation mappedTail parameter out : OTerm alpha),
 Nonempty (Derivation body []
 ((graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail ⊓
   (graph2 InternalPairing.pairing packed typ child ⊓
   (graph2 R observation packed parameter ⊓
   (graph2 InternalPairing.pairing typedObservation typ observation ⊓
    graph2 (argumentObservations R) mappedTail tail parameter)))).imp
 ((graph2 (argumentObservations R) out raw parameter).iff
   (graph2 InternalListCodec.consCode out typedObservation mappedTail))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
