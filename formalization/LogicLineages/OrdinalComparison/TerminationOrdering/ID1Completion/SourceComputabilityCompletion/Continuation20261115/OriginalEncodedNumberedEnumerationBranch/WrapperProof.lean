module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem recover (n : Nat) (labels heads types bases tuples extras out mappedHeads : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (programGraph (branch n) out ![labels,heads,types,bases,tuples,extras])))
    (hm : Nonempty (Derivation body Delta (graph1 (convertedHeads n) mappedHeads heads))) :
    Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out
      ![labels,mappedHeads,types,bases,tuples,extras])) := by
  let xs : Fin 6 → OTerm alpha := ![labels,heads,types,bases,tuples,extras]
  apply compositionRecover OriginalNumberedEnumerationBranch.branch
    ![.projection 0,.composition (convertedHeads n) ![.projection 1],.projection 2,.projection 3,.projection 4,.projection 5]
    out xs ![labels,mappedHeads,types,bases,tuples,extras] hv
  intro i
  fin_cases i
  · exact projectionValue 0 xs
  · apply compositionValue (convertedHeads n) ![.projection 1] mappedHeads xs ![heads] hm
    intro i
    fin_cases i
    exact projectionValue 1 xs
  · exact projectionValue 2 xs
  · exact projectionValue 3 xs
  · exact projectionValue 4 xs
  · exact projectionValue 5 xs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperProof
