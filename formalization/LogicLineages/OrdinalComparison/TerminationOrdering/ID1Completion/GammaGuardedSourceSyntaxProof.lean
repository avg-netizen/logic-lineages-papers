module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open GammaGuardedSource InternalGraphCompositionSyntaxProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (z suc zSubst sucSubst)

theorem literalGuardGraph {α : Type} (data : JointGammaComputability.Data) (x u : OTerm α) :
    literalGuard data x u = programGraph data.guard (suc z) ![x,u] := by
  unfold literalGuard SourcePresentation.checkerFormula
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceSyntaxProof
