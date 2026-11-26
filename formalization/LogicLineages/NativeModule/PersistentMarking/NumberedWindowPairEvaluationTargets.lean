module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPair
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPairEvaluationTargets
open LogicLineages.ComputabilityKnowledge List.Vector
open NumberedWindowArithmeticPair

def ActualPairProgram : Prop :=
  ∃ p : GorbowPRProgram.Program 2,
    ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = pair a b

/-- The program returns the canonical Encodable output for the complete optional
pair, including the failure result for every number outside the pair image. -/
def ActualPairDecoderProgram : Prop :=
  ∃ p : GorbowPRProgram.Program 1,
    ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (decode n)

end LogicLineages.PersistentMarking.NumberedWindowPairEvaluationTargets
