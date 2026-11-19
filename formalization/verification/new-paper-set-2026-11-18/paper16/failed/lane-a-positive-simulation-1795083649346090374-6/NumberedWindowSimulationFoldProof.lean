import LogicLineages.PersistentMarking.NumberedWindowSimulationBaseCases
import LogicLineages.PersistentMarking.NumberedWindowSimulationAbsCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationFAbsCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationSelectCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationFunCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationCopyCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationStatCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationMatchingCases
import LogicLineages.PersistentMarking.NumberedWindowSimulationCoverageCases
import LogicLineages.PersistentMarking.NumberedWindowSimulationMultisetCase
import LogicLineages.PersistentMarking.NumberedWindowSimulationWholeCases

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
