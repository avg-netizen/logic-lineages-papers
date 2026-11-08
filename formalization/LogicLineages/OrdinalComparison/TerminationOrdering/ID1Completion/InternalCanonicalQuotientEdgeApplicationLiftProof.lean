module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalQuotientEdgeApplicationLift InternalCanonicalQuotientEdgeApplicationLiftTargets
open InternalControlGraphSupportProof InternalApplicationStepPeelSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

 theorem actualOriginalCanonicalApplicationCalibration : ActualOriginalCanonicalApplicationCalibration :=
  InternalCanonicalQuotientEdgeApplicationLiftEvaluationProof.actualOriginalCanonicalApplicationCalibration

 theorem actualOriginalCanonicalRepresentativeApplicationTransport : ActualOriginalCanonicalRepresentativeApplicationTransport :=
  InternalCanonicalQuotientEdgeApplicationLiftRepresentativeProof.actualOriginalCanonicalRepresentativeApplicationTransport

 theorem actualOriginalCanonicalApplicationTypedOutput : ActualOriginalCanonicalApplicationTypedOutput :=
  InternalCanonicalQuotientEdgeApplicationLiftTypingProof.actualOriginalCanonicalApplicationTypedOutput

 theorem actualOriginalCanonicalEncodedQuotientEdgeApplicationLift : ActualOriginalCanonicalEncodedQuotientEdgeApplicationLift :=
  InternalCanonicalQuotientEdgeApplicationLiftEncodedProof.actualOriginalCanonicalEncodedQuotientEdgeApplicationLift

 theorem actualOriginalCanonicalQuotientEdgeApplicationLift : ActualOriginalCanonicalQuotientEdgeApplicationLift :=
  InternalCanonicalQuotientEdgeApplicationLiftWitnessProof.actualOriginalCanonicalQuotientEdgeApplicationLift

/-- Source typing and the SAME Edge first derive y's type; each exact J graph
then yields its codomain type. No target typing or new output invariant is assumed. -/
 theorem actualOriginalCanonicalQuotientEdgeApplicationTypedOutputs :
    ActualOriginalCanonicalQuotientEdgeApplicationTypedOutputs := by
  intro S data hm hc body sigma tau α Delta x y a certificate out other lifted
  let premise := liftPremises data sigma tau x y a certificate out other lifted
  have hp : Nonempty (Derivation body (premise :: Delta) premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hcore := andLeft hp
  have hx := andLeft hcore
  have ha := andLeft (andRight hcore)
  have he := andLeft (andRight (andRight hcore))
  have hy := InternalCanonicalQuotientEdgeSelectionTypingProof.typedPropagation
    data x y certificate (numeral (typeNumber (.arrow sigma tau))) hx he
  have hgraphs := andRight (andRight (andRight hcore))
  have ho := InternalCanonicalQuotientEdgeApplicationLiftTypingProof.applicationTypedOutput
    S data hm hc sigma tau x a out hx ha (andLeft hgraphs)
  have hv := InternalCanonicalQuotientEdgeApplicationLiftTypingProof.applicationTypedOutput
    S data hm hc sigma tau y a other hy ha (andRight hgraphs)
  obtain ⟨result⟩ := andIntro ho hv
  exact ⟨Derivation.implicationIntroduction result⟩

 theorem actualOriginalSelectedCanonicalQuotientEdgeApplicationLift :
    ActualOriginalSelectedCanonicalQuotientEdgeApplicationLift := by
  intro n arity symbols S Gamma table hc
  obtain ⟨data,hd,hs,hprevious⟩ :=
    InternalCanonicalQuotientEdgeSelectionProof.actualOriginalCanonicalEdgeSelection
      n arity symbols S Gamma table hc
  refine ⟨data,hd,hs,actualOriginalCanonicalApplicationCalibration
    n arity symbols S Gamma table data hc hd,hprevious,?_⟩
  intro body sigma tau α Delta
  exact ⟨actualOriginalCanonicalApplicationTypedOutput S data hd.2.1 hc body sigma tau α Delta,
    actualOriginalCanonicalQuotientEdgeApplicationLift S data hd.2.1 hc body sigma tau α Delta,
    actualOriginalCanonicalQuotientEdgeApplicationTypedOutputs S data hd.2.1 hc body sigma tau α Delta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftProof
