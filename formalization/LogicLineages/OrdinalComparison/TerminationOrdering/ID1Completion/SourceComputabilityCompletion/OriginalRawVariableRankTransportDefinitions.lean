module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Proof-side simultaneous induction over the two existing modifying modes. -/
def transformMode (erasing : Bool) : Mode := if erasing then .erase else .shift

/-- Weak arithmetic comparison uses the original strict order below successor. -/
def RankRelation {alpha : Type} (erasing : Bool) (after before : OTerm alpha) : Formula alpha :=
  if erasing then InternalLessThan.strictLess after (OrdinaryArithmetic.succTerm before)
  else equal after before

def transportMatrix {alpha : Type} (p : Program 3) (erasing : Bool) (raw : OTerm alpha) :
    Formula (alpha ⊕ Fin 5) :=
  (graph3 p (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1)) (raw.relabel Sum.inl) ⊓
    (graph1 variableRankRaw (.var (.inr 3)) (raw.relabel Sum.inl) ⊓
      graph1 variableRankRaw (.var (.inr 4)) (.var (.inr 2)))).imp
    (RankRelation erasing (.var (.inr 4)) (.var (.inr 3)))

def AtRaw {alpha : Type} (p : Program 3) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (transportMatrix p erasing raw)

def rawPredicate {alpha : Type} (p : Program 3) (erasing : Bool) : Formula (alpha ⊕ Fin 1) :=
  AtRaw p erasing (.var (.inr 0))

def BelowRaw {alpha : Type} (p : Program 3) (erasing : Bool) (raw : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (rawPredicate p erasing) raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransport
