module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationPartsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ObservationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
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


/-- Only the requested type, Gamma/count, and actual bounds components change;
all original seed/parameter/source observations are retained literally. -/
def frame (xs : Fin 11 → OTerm alpha) (typ gamma count pair size label : OTerm alpha) : Fin 11 → OTerm alpha :=
  ![xs 0,xs 1,xs 2,xs 3,xs 4,typ,gamma,count,pair,size,label]

theorem child (n : Nat) (arity : Fin n → Nat) (H : Program 1) (parentMode childMode : Bool)
    (raw child typ gamma count pair size label : OTerm alpha) (xs : Fin 11 → OTerm alpha)
    (ho : Nonempty (Derivation body Delta (observations n arity H parentMode raw xs)))
    (ha : Nonempty (Derivation body Delta (accepted n arity H childMode typ child gamma (xs 2))))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)))
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) pair child)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size label))) :
    Nonempty (Derivation body Delta (observations n arity H childMode child (frame xs typ gamma count pair size label))) :=
  ObservationsProof.assemble n arity H childMode child (frame xs typ gamma count pair size label)
    (ObservationPartsProof.context n arity H parentMode raw xs ho)
    (ObservationPartsProof.types n arity H parentMode raw xs ho)
    (ObservationPartsProof.heads n arity H parentMode raw xs ho)
    (ObservationPartsProof.closed n arity H parentMode raw xs ho) ha hl hb hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ChildFrameProof
