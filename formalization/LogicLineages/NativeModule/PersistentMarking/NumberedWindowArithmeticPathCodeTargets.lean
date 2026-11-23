module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPathCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeTargets
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticRawWitnessCodeTargets

def ExactRawHopCodec : Prop := LiteralWitnessCodec encodeRawHop decodeRawHop

def ExactClassEdgeWitnessCodec : Prop := LiteralWitnessCodec encodeClassEdge decodeClassEdge

def ExactClassHopCodec : Prop := LiteralWitnessCodec encodeClassHop decodeClassHop

def ExactRawPathListCodec : Prop := LiteralWitnessCodec encodeRawPath decodeRawPath

def ExactClassPathListCodec : Prop := LiteralWitnessCodec encodeClassPath decodeClassPath

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeTargets
