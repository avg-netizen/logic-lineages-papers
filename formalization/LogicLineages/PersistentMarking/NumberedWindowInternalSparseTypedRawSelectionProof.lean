module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawPackedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramProof
import LogicLineages.PersistentMarking.NumberedWindowConcreteRulePrograms
import LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickFallbackChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)
open NumberedWindowInternalSparseRawTickFallbackChecks (exact_ConcreteFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax)
open NumberedWindowInternalSparseTypedRawChecks (exact_TypedRaw5Calibration)
open NumberedWindowInternalSparseTypedRawPackedWindowProof (packedWindowWitness)
open NumberedWindowInternalSparseTypedRawSelectionTargets

theorem chosen : ExactConcreteTypedRaw5 := by
  intro entries s
  have rootChoice : ∃ root : Program 3, ActualRoot (NumberedWindowConcreteCheckers.root entries s) root :=
    NumberedWindowRootDispatchProgramProof.program (NumberedWindowRootDispatchAlgorithm.fixed entries s.window.2)
      (NumberedWindowConcreteRulePrograms.primitive entries s.window.2)
  have syntaxChoice : ∃ syn : Program 1, ActualRawSyntax syn :=
    NumberedWindowSyntaxProgramProof.termProgram
  obtain ⟨root,rootCal⟩ := rootChoice
  obtain ⟨other,otherCal⟩ := exact_ConcreteFallback
  obtain ⟨windowProg,windowCal⟩ := packedWindowWitness s
  obtain ⟨syntaxProg,syntaxCal⟩ := syntaxChoice
  exact ⟨root,other,windowProg,syntaxProg,rootCal,otherCal,syntaxCal,windowCal,
    exact_TypedRaw5Calibration entries s root other windowProg syntaxProg
      rootCal otherCal syntaxCal windowCal⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawSelectionProof
