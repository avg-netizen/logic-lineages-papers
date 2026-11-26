module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem sixRename {alpha beta : Type} (p : Program 6) (out a b c d e f : OTerm alpha) (j : alpha → beta) :
    (programGraph p out ![a,b,c,d,e,f]).relabel j =
    programGraph p (out.relabel j) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
  rw [InternalControlGraphSupportProof.programRename]
  have hv : (fun i : Fin 6 => (![a,b,c,d,e,f] i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j,f.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
  rw [hv]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SyntaxProof
