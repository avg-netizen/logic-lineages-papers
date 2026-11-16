module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem context (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context (xs 2) (xs 0) (xs 1))) := (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft h)))))))

theorem types (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types (xs 3) (xs 0) (xs 1))) := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft h)))))))

theorem heads (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) (xs 4) (xs 0) (xs 1))) := (andRight (andLeft (andLeft (andLeft (andLeft (andLeft h))))))

theorem closed (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed (xs 3))) := (andRight (andLeft (andLeft (andLeft (andLeft h)))))

theorem admission (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (accepted n arity H arguments (xs 5) raw (xs 6) (xs 2))) := (andRight (andLeft (andLeft (andLeft h))))

theorem length (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length (xs 7) (xs 6))) := (andRight (andLeft (andLeft h)))

theorem bounds (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) (xs 8) raw)) := (andRight (andLeft h))

theorem pairing (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (observations n arity H arguments raw xs))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (xs 8) (xs 9) (xs 10))) := (andRight h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
