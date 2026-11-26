module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeHeadsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NativeSupportProof NativeBranchesProof NativeHeadsProof

theorem nativeLayer : Targets.NativeLayer := by
  intro n types heads labels tupleBound variableBound prior opened
  have h0 := variablesValue n types heads labels tupleBound variableBound prior opened
  have h1 := lambdasValue n types heads labels tupleBound variableBound prior opened
  have h2 := applicationsValue n types heads labels tupleBound variableBound prior opened
  have h3 := bottomsValue n types heads labels tupleBound variableBound prior opened
  have h4 := ordinaryValue n types heads labels tupleBound variableBound prior opened
  have h5 := numberedValue n types heads labels tupleBound variableBound prior opened
  have h6 := nilsValue n types heads labels tupleBound variableBound prior opened
  have h7 := argumentConsValue n types heads labels tupleBound variableBound prior opened
  have j1 := joinEncoding _ _ _ _ _ h0 h1
  have j2 := joinEncoding _ _ _ _ _ j1 h2
  have j3 := joinEncoding _ _ _ _ _ j2 h3
  have j4 := joinEncoding _ _ _ _ _ j3 h4
  have j5 := joinEncoding _ _ _ _ _ j4 h5
  have j6 := joinEncoding _ _ _ _ _ j5 h6
  have j7 := joinEncoding _ _ _ _ _ j6 h7
  exact j7
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.NativeProof
