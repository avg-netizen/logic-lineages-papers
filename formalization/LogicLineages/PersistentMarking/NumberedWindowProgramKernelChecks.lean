module

public import LogicLineages.PersistentMarking.NumberedWindowRegistryPairPrograms

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
open LogicLineages.ComputabilityKnowledge List.Vector

theorem polynomial : ∃ p : GorbowPRProgram.Program 2,
    ∀ a b, GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ List.Vector.nil) = NumberedWindowPairAlgorithm.pair a b :=
  NumberedWindowRegistryPairPrograms.literalEncoding

theorem completeDecoding : ∃ p : GorbowPRProgram.Program 1,
    ∀ n, GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (NumberedWindowPairAlgorithm.decode n) :=
  NumberedWindowRegistryPairPrograms.literalDecoding
#print axioms polynomial
#print axioms completeDecoding
end LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
