module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
abbrev T (n : Nat) (arity : Fin n → Nat) : Program 2 := OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
abbrev Q (n : Nat) (arity : Fin n → Nat) : Program 2 := OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)
abbrev E (n : Nat) (arity : Fin n → Nat) : Program 3 := OriginalConcreteStructuralEdge.edge n arity
abbrev L (n : Nat) (arity : Fin n → Nat) : Program 2 := SeededPrimaryPool.primary (T n arity) (Q n arity) (E n arity)
abbrev P (n : Nat) (arity : Fin n → Nat) : Program 3 := TwoSol20261113.CalibratedPrimary.Membership.classTest (T n arity) (L n arity) (TransparentCandidate.candidate (T n arity))
abbrev R (n : Nat) (arity : Fin n → Nat) : Program 2 := OriginalTransparentMinimum.minimum (T n arity) (P n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence
