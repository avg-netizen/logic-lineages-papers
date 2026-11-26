module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Definitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def fieldsSchema (C : Program 1) (E : Program 2)
    (source target node rev window symbols types : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing node source target ⊓
  (graph2 InternalPairing.pairing rev target source ⊓
  (graph2 InternalPairing.pairing window symbols types ⊓
  (graph1 C (suc z) source ⊓ (graph1 C (suc z) target ⊓
  (WindowSourceHeadInclusion.ArrowClosed types ⊓ graph2 E (suc z) node window)))))
def matrixSchema (C : Program 1) (E : Program 2) (source : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  let x : Fin 6 → OTerm (alpha ⊕ Fin 6) := fun i => .var (.inr i)
  (fieldsSchema C E (source.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).imp
    (graph2 E (suc z) (x 2) (x 3))
def allSchema (C : Program 1) (E : Program 2) (source : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrixSchema C E source)
abbrev fields (n : Nat) (arity : Fin n → Nat) := fieldsSchema (alpha := alpha)
  (OriginalCodeValidityGuard.check n) (OriginalDecodedExchangeEquation.exchange n arity)
abbrev matrix (n : Nat) (arity : Fin n → Nat) := matrixSchema (alpha := alpha)
  (OriginalCodeValidityGuard.check n) (OriginalDecodedExchangeEquation.exchange n arity)
abbrev AtRaw (n : Nat) (arity : Fin n → Nat) := allSchema (alpha := alpha)
  (OriginalCodeValidityGuard.check n) (OriginalDecodedExchangeEquation.exchange n arity)
def predicate (n : Nat) (arity : Fin n → Nat) : Formula (alpha ⊕ Fin 1) := AtRaw n arity (.var (.inr 0))
def BelowRaw (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n arity) source

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Definitions
