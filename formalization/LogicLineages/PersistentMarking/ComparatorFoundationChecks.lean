import LogicLineages.PersistentMarking.ComparisonFoundationProof
import LogicLineages.PersistentMarking.BridgeTypingProof
import LogicLineages.PersistentMarking.OpeningFoundationProof
import LogicLineages.PersistentMarking.DecodeRoundtripProof
namespace LogicLineages.PersistentMarking.ComparatorFoundationChecks

theorem fixedRankedArity : ComparisonTargets.FixedRankedArity := ComparisonFoundationProof.fixedRankedArity
theorem nativeEquivalent : ComparisonTargets.NativeEquivalent := ComparisonFoundationProof.nativeEquivalent
theorem nativeAboveApplication : ComparisonTargets.NativeAboveApplication := ComparisonFoundationProof.nativeAboveApplication
theorem rankedAboveNative : ComparisonTargets.RankedAboveNative := ComparisonFoundationProof.rankedAboveNative
theorem removeLength : ComparisonTargets.RemoveLength := ComparisonFoundationProof.removeLength
theorem splitLength : ComparisonTargets.SplitLength := ComparisonFoundationProof.splitLength
theorem encodeTypingExact : BridgeTargets.EncodeTypingExact := BridgeTypingProof.encodeTypingExact
theorem decodeTyping : BridgeTargets.DecodeTyping := BridgeTypingProof.decodeTyping
theorem encodeValidityExact : BridgeTargets.EncodeValidityExact := BridgeTypingProof.encodeValidityExact
theorem typedClosedScoped : BridgeTargets.TypedClosedScoped := OpeningFoundationProof.typedClosedScoped
theorem openingTyped : BridgeTargets.OpeningTyped := OpeningFoundationProof.openingTyped
theorem freshOpeningExists : BridgeTargets.FreshOpeningExists := OpeningFoundationProof.freshOpeningExists

theorem encodeDecodeScoped : BridgeTargets.EncodeDecodeScoped := DecodeRoundtripProof.encodeDecodeScoped

#print axioms encodeDecodeScoped
#print axioms fixedRankedArity
#print axioms nativeEquivalent
#print axioms nativeAboveApplication
#print axioms rankedAboveNative
#print axioms removeLength
#print axioms splitLength
#print axioms encodeTypingExact
#print axioms decodeTyping
#print axioms encodeValidityExact
#print axioms typedClosedScoped
#print axioms openingTyped
#print axioms freshOpeningExists
end LogicLineages.PersistentMarking.ComparatorFoundationChecks
