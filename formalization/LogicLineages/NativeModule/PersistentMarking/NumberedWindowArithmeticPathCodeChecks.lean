module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticClassHopCodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeChecks
open NumberedWindowArithmeticCodecLaws NumberedWindowArithmeticWitnessListCodeProof
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticPathCodeTargets
open NumberedWindowArithmeticRawHopCodeProof NumberedWindowArithmeticClassHopCodeProof

theorem exact_RawHopCodec : ExactRawHopCodec :=
  codec encodeRawHop decodeRawHop rawRead rawRound

theorem exact_ClassEdgeWitnessCodec : ExactClassEdgeWitnessCodec :=
  codec encodeClassEdge decodeClassEdge edgeRead edgeRound

theorem exact_ClassHopCodec : ExactClassHopCodec :=
  codec encodeClassHop decodeClassHop hopRead hopRound

theorem exact_RawPathListCodec : ExactRawPathListCodec :=
  codec encodeRawPath decodeRawPath
    (decodeSound encodeRawHop decodeRawHop rawRead)
    (decodeRound encodeRawHop decodeRawHop rawRound)

theorem exact_ClassPathListCodec : ExactClassPathListCodec :=
  codec encodeClassPath decodeClassPath
    (decodeSound encodeClassHop decodeClassHop hopRead)
    (decodeRound encodeClassHop decodeClassHop hopRound)

#print axioms exact_RawHopCodec
#print axioms exact_ClassEdgeWitnessCodec
#print axioms exact_ClassHopCodec
#print axioms exact_RawPathListCodec
#print axioms exact_ClassPathListCodec

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeChecks
