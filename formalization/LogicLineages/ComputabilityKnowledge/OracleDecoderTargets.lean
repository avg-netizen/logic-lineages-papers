module

public import LogicLineages.ComputabilityKnowledge.OracleDecoderDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleDecoderTargets
open OracleProgram OracleDecoder

def OracleDecoderComplete : Prop := ∀ p : Program, decode (OracleProgram.encode p) = some p

def OracleDecoderSound : Prop := ∀ (i : Nat) (p : Program), decode i = some p → OracleProgram.encode p = i

def PrimitiveRecursiveValidity : Prop := Primrec validIndex

def PrimitiveRecursiveEncodedDecoder : Prop := Primrec encodedDecode

end LogicLineages.ComputabilityKnowledge.OracleDecoderTargets
