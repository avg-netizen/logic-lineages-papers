module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.InductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type}
/-- Exactly the existing universe mode, with actual guarded source programs. -/
def accepted (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (typ raw gamma context : OTerm alpha) : Formula alpha :=
  if arguments then OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context
  else OriginalUniverseDecoderInternalAcceptance.TermAccepted H
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context
/-- Coordinate layout: seed,param,Context,allowedTypes,encodedHeads,requestedType(s),
Gamma,GammaLength,boundsPair,size,maxLabel. All are universally bound actual values. -/
def observations (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula alpha :=
  graph2 OriginalClassCodes.context (xs 2) (xs 0) (xs 1) ⊓
  graph2 OriginalClassCodes.types (xs 3) (xs 0) (xs 1) ⊓
  graph2 (OriginalClassCodes.heads n arity) (xs 4) (xs 0) (xs 1) ⊓
  Continuation20261114.WindowSourceHeadInclusion.ArrowClosed (xs 3) ⊓
  accepted n arity H arguments (xs 5) raw (xs 6) (xs 2) ⊓
  graph1 OriginalContextInsertion.length (xs 7) (xs 6) ⊓
  graph1 (Continuation20261115.OriginalCodeBoundsRecursion.bounds n) (xs 8) raw ⊓
  graph2 InternalPairing.pairing (xs 8) (xs 9) (xs 10)
/-- Capacity premises are nested in the RESULT, not needed to obtain child
validity/positivity. This prevents circular use of guarded parent bounds. -/
def capacityBody (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  (InternalLessThan.strictLess ((xs 9).relabel Sum.inl) (suc (.var (.inr 1))) ⊓
   InternalLessThan.strictLess ((xs 10).relabel Sum.inl) (suc (.var (.inr 0)))).imp
    (OriginalEnumerationFields.Targets.accepted n (raw.relabel Sum.inl) ((xs 7).relabel Sum.inl)
      ((xs 3).relabel Sum.inl) ((xs 4).relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)))
def capacity (n : Nat) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (capacityBody n raw xs)
/-- Actual original guard plus mode-specific original size facts, proved from
source admission. Argument list facts use its own size, not a false depth bound. -/
def intrinsic (n : Nat) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula alpha :=
  graph1 (Continuation20261115.OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
    (if arguments then OriginalEnumerationFields.Targets.typesAllowed (xs 5) (xs 3) (xs 9)
     else InternalLessThan.strictLess z (xs 9))
def result (n : Nat) (arguments : Bool) (raw : OTerm alpha) (xs : Fin 11 → OTerm alpha) : Formula alpha :=
  intrinsic n arguments raw xs ⊓ capacity n raw xs
def matrix (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 11) :=
  (observations n arity H arguments (raw.relabel Sum.inl) (fun i => .var (.inr i))).imp
    (result n arguments (raw.relabel Sum.inl) (fun i => .var (.inr i)))
def AtMode (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n arity H arguments raw)
def AtRaw (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) : Formula alpha :=
  AtMode n arity H false raw ⊓ AtMode n arity H true raw
def predicate (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Formula (alpha ⊕ Fin 1) :=
  AtRaw n arity H (.var (.inr 0))
def BelowRaw (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n arity H) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Induction
