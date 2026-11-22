module
public import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialTargets
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesProof
import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizedTerminalProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedExistential
open OriginalPrintedTerminalBitClauses (exactPrintedNormalizedBoolClauses)
open OriginalPrintedCircuitNormalizedTerminal (exactPrintedNormalizedTerminal)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedCircuitSequential (LeavesExternal)
open ArbitraryHeadWireList (Agrees)

theorem exactOriginalLiteralFamilyExistential : ExactOriginalLiteralFamilyExistential := by
  intro f known gates p plain positive
  constructor
  · rintro ⟨θ,literal⟩
    exact ⟨θ,(exactPrintedNormalizedBoolClauses f θ known gates p plain positive).mpr literal⟩
  · rintro ⟨θ,original⟩
    exact ⟨θ,(exactPrintedNormalizedBoolClauses f θ known gates p plain positive).mp original⟩

theorem exactOriginalTypedObservationExistential : ExactOriginalTypedObservationExistential := by
  intro f known gates p topo plain positive
  constructor
  · rintro ⟨θ,graph,terminal⟩
    have lifted := exactPrintedNormalizedTerminal f known gates topo θ (.rows p) plain positive
    exact ⟨θ,lifted.mpr ⟨θ,θ,fun _ _ => rfl,graph,fun _ _ => rfl,fun _ _ => rfl,terminal⟩⟩
  · rintro ⟨base,observed⟩
    obtain ⟨_,θ,_,graph,_,_,terminal⟩ :=
      (exactPrintedNormalizedTerminal f known gates topo base (.rows p) plain positive).mp observed
    exact ⟨θ,graph,terminal⟩

end LogicLineages.PermittedControl.OriginalPrintedTypedExistential
