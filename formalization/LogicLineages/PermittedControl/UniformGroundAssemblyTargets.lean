module
public import LogicLineages.PermittedControl.UniformGroundComparisonTargets
public import LogicLineages.PermittedControl.UniformPolicyCompilerTargets
public import LogicLineages.PermittedControl.ClosedBlockDecisionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.UniformGroundAssembly
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion

/-- The near controls decided jointly: one computable function of the
parameter `b` and the encoded closed-block query. -/
def JointNearClosedBlocks : Prop :=
  ∃ decide : Nat × OriginalPrintedRawFamilyFrontend.Args → Option Bool, Computable decide ∧
    ∀ b : Nat, ClosedBlockDecision.Decides (nearControl b) (fun x => decide (b,x))

/-- The uniform ground comparison from exactly two pieces: a source compiler
taking the policy program as input, and the joint near-control decision.
Everything else (generated sources, ground domain, positive-coordinate test,
canonical reduction, scalar-to-circuit compiler, closed-block decision at
the factorial control) is used as accepted. -/
def ExactUniformGroundFromPieces : Prop :=
  UniformPolicyCompiler.ExactUniformCompiler → JointNearClosedBlocks →
    UniformGroundComparison.UniformGroundComparison

def ExactUniformMainFromPieces : Prop :=
  UniformPolicyCompiler.ExactUniformCompiler → JointNearClosedBlocks →
    UniformGroundComparison.UniformMainComparison

end LogicLineages.PermittedControl.UniformGroundAssembly
