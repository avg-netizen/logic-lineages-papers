module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative GuardedSource GuardedSourceGround

/-- Original scalar membership closes downward through the literal existential
certificateGraph, for arbitrary source Programs, context and open terms.
No calibration or external accessibility premise is supplied. -/
def ActualScalarDownward : Prop :=
  ∀ (source : SourcePresentation.Data) (context : Nat) (α : Type)
    (x y : OrdinaryArithmetic.Term α),
  Nonempty (Derivation (SourcePresentation.sourceBody source context) []
    ((literalGround x ⊓ literalR source context x y).imp (literalGround y)))

/-- Syntactic identity of the ORIGINAL computability formula at ground. -/
def ActualGroundFormula : Prop :=
  ∀ (comp : JointGammaComputability.Data) (context : Nat) (α : Type)
    (x : OrdinaryArithmetic.Term α),
  literalComputable comp context .ground x =
    (literalTyped comp context (numeral (typeNumber .ground)) x ⊓ literalGround x)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundTargets
