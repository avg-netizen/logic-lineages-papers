module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115 Continuation20261116

/-- Same actual context/window at every recursive child; gamma can vary under lambda. -/
def environment {alpha : Type} (n : Nat) (context symbols types window : OTerm alpha) : Formula alpha :=
  graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) context ⊓
    (graph1 OriginalGuardedHeadSourceCoverage.contextSymbols symbols context ⊓
      (graph1 OriginalUniverseDomainCoverage.contextTypes types context ⊓
        graph2 InternalPairing.pairing window symbols types))

def edge {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source target node window : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing node source target ⊓
    (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source ⊓
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target ⊓
        graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window))

def accepted {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) : Formula alpha :=
  OriginalUniverseDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    arguments typ raw gamma context

def plain {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (typ raw gamma : OTerm alpha) : Formula alpha :=
  OriginalTypedDecoderTransport.Accepted (OriginalConcreteHeadSignature.signature n arity)
    arguments typ raw gamma

/-- All child-context/type parameters are bound, never preserved as an oracle. -/
def row {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source typ target gamma context symbols types window node : OTerm alpha) : Formula alpha :=
  (environment n context symbols types window ⊓ edge n arity source target node window).imp
    ((accepted n arity arguments typ source gamma context ⊓ plain n arity arguments typ target gamma).imp
      (accepted n arity arguments typ target gamma context))

def matrix {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
  let x : Fin 8 → OTerm (alpha ⊕ Fin 8) := fun i => .var (.inr i)
  row n arity arguments (source.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
def AtMode {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool) (source : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n arity arguments source)
def AtRaw {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula alpha :=
  AtMode n arity false source ⊓ AtMode n arity true source
def predicate {alpha : Type} (n : Nat) (arity : Fin n → Nat) : Formula (alpha ⊕ Fin 1) := AtRaw n arity (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n arity) source
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Induction
