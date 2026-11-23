module

public import LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawRootCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowStatTargets
open NumberedWindowSyntax NumberedWindowStatAlgorithm
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticWitnessListCode NumberedWindowPrimitiveWitnessBits

def encodePartition (w : ReplacementWitness) : Partition :=
  (w.kept.map encodeTerm,w.removed.map encodeTerm,w.added.map encodeTerm)

def ExactArgsView : Prop := ∀ n, argsView n =
  (decodeArgs n).map (fun qs => qs.toList.map encodeTerm)

def ExactPartitionView : Prop := ∀ n, readPartition n = (decodeReplacement n).map encodePartition

def ExactMark : Prop := ∀ q r, mark q r =
  (decodeTerm q).any (fun Q => (decodeTerm r).any (markBit Q))

def ExactReplacement : Prop := ∀ q w r, replacement q w r =
  (decodeArgs q).any (fun qs => (decodeReplacement w).any (fun p =>
    (decodeArgs r).any (fun rs => replacementBit qs rs p)))

end LogicLineages.PersistentMarking.NumberedWindowStatTargets
