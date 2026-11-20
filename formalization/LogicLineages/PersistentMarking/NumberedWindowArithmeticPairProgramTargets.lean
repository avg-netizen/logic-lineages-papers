import LogicLineages.PersistentMarking.NumberedWindowArithmeticPair
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets
open LogicLineages.ComputabilityKnowledge List.Vector
open NumberedWindowArithmeticPair

def PairAndDecodeCalibration : Prop :=
  (∀ a b, pair a b = GorbowRegistryTuple.pair a b) ∧
  (∀ n, decode n = GorbowRegistryDecoder.decodePair n)

def ActualPairProgram : Prop :=
  ∃ p : GorbowPRProgram.Program 2,
    ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = pair a b

/-- The program returns the canonical Encodable output for the complete optional
pair, including the failure result for every number outside the pair image. -/
def ActualPairDecoderProgram : Prop :=
  ∃ p : GorbowPRProgram.Program 1,
    ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (decode n)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairProgramTargets
