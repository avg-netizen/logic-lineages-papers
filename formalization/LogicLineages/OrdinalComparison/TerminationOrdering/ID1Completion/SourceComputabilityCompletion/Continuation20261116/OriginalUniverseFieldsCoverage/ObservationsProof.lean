module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
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

theorem assemble (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h0 : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context (xs 2) (xs 0) (xs 1))))
    (h1 : Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types (xs 3) (xs 0) (xs 1))))
    (h2 : Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) (xs 4) (xs 0) (xs 1))))
    (h3 : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed (xs 3))))
    (h4 : Nonempty (Derivation body Delta (accepted n arity H arguments (xs 5) raw (xs 6) (xs 2))))
    (h5 : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length (xs 7) (xs 6))))
    (h6 : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) (xs 8) raw)))
    (h7 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (xs 8) (xs 9) (xs 10)))) :
    Nonempty (Derivation body Delta (observations n arity H arguments raw xs)) :=
  andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro h0 h1) h2) h3) h4) h5) h6) h7

theorem intrinsicGuard (n : Nat) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (result n arguments raw xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)) :=
  andLeft (andLeft h)

theorem termPositive (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (result n false raw xs))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z (xs 9))) := andRight (andLeft h)

theorem argumentTypes (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (result n true raw xs))) :
    Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.typesAllowed (xs 5) (xs 3) (xs 9))) :=
  andRight (andLeft h)

theorem enclosing (n : Nat) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (result n arguments raw xs))) :
    Nonempty (Derivation body Delta (capacity n raw xs)) := andRight h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
