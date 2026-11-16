module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Lists
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {alpha : Type}
def matrix (n : Nat) (list bound fuel types heads labels tupleBound : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  let raw : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let member := graph2 contains (numeral 1) (list.relabel Sum.inl) raw
  let meaning := Meaning.holds n raw (bound.relabel Sum.inl) (fuel.relabel Sum.inl)
    (types.relabel Sum.inl) (heads.relabel Sum.inl) (labels.relabel Sum.inl) (tupleBound.relabel Sum.inl)
  member.imp meaning ⊓ meaning.imp member
def Characterizes (n : Nat) (list bound fuel types heads labels tupleBound : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n list bound fuel types heads labels tupleBound)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.Lists
