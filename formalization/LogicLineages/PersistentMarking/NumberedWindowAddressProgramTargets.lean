module

public import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowAddressAlgorithm List.Vector

def TypeCodeProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = (typeBit n).toNat

def ContextCodeProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (contextView n)

def AddressCodeProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (addressView n)

end LogicLineages.PersistentMarking.NumberedWindowAddressProgramTargets
