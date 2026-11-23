module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationBaseCases
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationAbsCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFAbsCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationSelectCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationFunCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationCopyCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationStatCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationMatchingCases
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationCoverageCases
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationMultisetCase
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationWholeCases

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationFoldProof
open LiteralDerivationTree NumberedWindowSimulationJobs

/-- Direct structural fold over the exact six-sort finite witness.
Every local constructor proof consumes only its actual child jobs,
including both independent Stat subtrees. -/
theorem all (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    {J : Judgment} (d : Tree S J) : Job S K d :=
  Tree.rec (motive := fun _ t => Job S K t)
    (@NumberedWindowSimulationBaseCases.varCase S K hk)
    (@NumberedWindowSimulationAbsCase.abs S K hk)
    (@NumberedWindowSimulationFunCase.funHead S K hk)
    (@NumberedWindowSimulationBaseCases.put S K)
    (@NumberedWindowSimulationSelectCase.select S K hk)
    (@NumberedWindowSimulationFAbsCase.fabs S K hk)
    (@NumberedWindowSimulationCopyCase.copy S K hk)
    (@NumberedWindowSimulationStatCase.stat S K hk)
    (@NumberedWindowSimulationBaseCases.strict S K hk)
    (@NumberedWindowSimulationMatchingCases.nil S K)
    (@NumberedWindowSimulationMatchingCases.cons S K)
    (@NumberedWindowSimulationMultisetCase.replace S K)
    (@NumberedWindowSimulationCoverageCases.nil S K)
    (@NumberedWindowSimulationCoverageCases.cons S K)
    (@NumberedWindowSimulationWholeCases.nil S K)
    (@NumberedWindowSimulationWholeCases.cons S K)
    d

end LogicLineages.PersistentMarking.NumberedWindowSimulationFoldProof
