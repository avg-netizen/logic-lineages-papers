module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceRelationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof GammaGuardedSource
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Forward transport of the original SAME-Gamma guard along the original
positive relation. The target typedness supplies target-object validity;
all Programs, type codes, contexts and input terms remain arbitrary. -/
def ActualOriginalForwardGuardTransport : Prop :=
  ∀ (oldSource : SourcePresentation.Data) (oldComp : JointGammaComputability.Data)
    (valid gamma : Program 1) (tag : Program 2) (window : Program 1)
    (context : Nat) (α : Type) (typ x y u : OrdinaryArithmetic.Term α),
  let src := source oldSource oldComp.typed valid gamma tag window
  let comp := computability oldComp valid gamma tag
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    (((GuardedSource.literalTyped comp context typ y ⊓ GuardedSource.literalR src context x y) ⊓
      literalGuard comp x u).imp (literalGuard comp y u)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ForwardGuardTargets
