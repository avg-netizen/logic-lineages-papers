module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowAnnotationAlgorithm List.Vector

def HeadDeclarationProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (headOutput n)

def AnnotationProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (output n)

end LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramTargets
