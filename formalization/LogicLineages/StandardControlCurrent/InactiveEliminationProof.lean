module
public import LogicLineages.StandardControlCurrent.InactiveEliminationBlockProof
public import LogicLineages.StandardControlCurrent.InactiveEliminationProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationProof
 theorem full : InactiveEliminationTargets.Full :=
  ⟨InactiveEliminationCleaningProof.cleaning,
   InactiveEliminationSemanticProof.actualNormalization,
   InactiveEliminationCandidateProof.candidateCompleteness,
   InactiveEliminationSemanticProof.elimination,
   InactiveEliminationSemanticProof.support,
   InactiveEliminationBlockProof.blockProgress,
   InactiveEliminationSemanticProof.guardedAtom,
   InactiveEliminationProgramsProof.programs⟩
end LogicLineages.StandardControlCurrent.InactiveEliminationProof
