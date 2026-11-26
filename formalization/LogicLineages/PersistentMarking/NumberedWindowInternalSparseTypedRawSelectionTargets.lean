module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)

/-- Choose actual callee programs on the original shared source settings.
The output raw checker is the literal typedRaw5 applied to these specific
programs: no separate extensionally equivalent raw witness can be used. -/
def ExactConcreteTypedRaw5 : Prop :=
  ∀ (entries : Entries) (s : Settings),
    ∃ (root other windowProg : Program 3) (syntaxProg : Program 1),
      ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
      ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
      ActualRawCalibration entries s (typedRaw5 root other windowProg syntaxProg)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionTargets
