module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsConstructorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalCoverArgumentCellsTargets (cellsAt cellsReport)
open NumberedWindowInternalCoverArgumentCellsConstructorProof (paired)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepTape)
open NumberedWindowInternalCoverSelectedGrammarNonemptyArgsTargets

attribute [local irreducible] programGraph

theorem exact_OpenSelectedNonemptyArgsRow : ExactOpenSelectedNonemptyArgsRow := by
  intro body α Γ out H K ids terms args q tail run hq ha
  let xs := stepTape H K ids terms args
  let slots := (![3,4] : Fin 2 → Fin 5)
  have actual := recoverReordered cellsAt slots out xs run
  have tape : (fun i => xs (slots i)) = ![terms,args] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at actual
  exact paired out terms args q tail actual hq ha

#print axioms exact_OpenSelectedNonemptyArgsRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNonemptyArgsRowProof
