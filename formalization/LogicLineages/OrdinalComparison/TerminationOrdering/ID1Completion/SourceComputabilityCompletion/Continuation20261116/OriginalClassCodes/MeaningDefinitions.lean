module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Meaning
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The exact twelve conjuncts of the frozen witness block, in original order. -/
def observations {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) (xs : Fin 9 → OTerm alpha) : Formula alpha :=
  graph2 rootType (xs 1) seed param ⊓
  graph2 types (xs 2) seed param ⊓
  graph2 (heads n arity) (xs 3) seed param ⊓
  graph2 (size n) (xs 4) seed param ⊓
  graph2 (labels n) (xs 5) seed param ⊓
  graph2 bound (xs 6) seed param ⊓
  graph2 (fuel n) (xs 7) seed param ⊓
  graph2 (admitted n H) (xs 8) seed param ⊓
  (eqn (xs 8) (numeral 0)).not ⊓
  graph2 InternalPairing.pairing candidate (xs 1) (xs 0) ⊓
  OriginalEnumerationFields.Targets.accepted n (xs 0) (xs 6) (xs 2) (xs 3) (xs 5) (xs 4) ⊓
  OriginalEnumerationMembership.Targets.depthBound n (xs 0) (xs 7)
def matrix {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (seed param candidate : OTerm alpha) : Formula (alpha ⊕ Fin 9) :=
  observations n arity H (seed.relabel Sum.inl) (param.relabel Sum.inl) (candidate.relabel Sum.inl)
    (fun i => .var (.inr i))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Meaning
