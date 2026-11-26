module

public import LogicLineages.PersistentMarking.NumberedWindowAdmissionAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowAdmissionAlgorithm List.Vector

/-- The input encodes the two finite numeral lists together with the term or Args code. -/
def AdmissionProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ w n,
  GorbowPRProgram.evaluate p (Encodable.encode (w,n) ::ᵥ List.Vector.nil) =
    Encodable.encode (bits w n)

end LogicLineages.PersistentMarking.NumberedWindowAdmissionProgramTargets
