module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCode
public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmTargets
open NumberedWindowSyntaxAlgorithm NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTermCode

def ExactNominalHeadGuard : Prop := ∀ n, headBit n = (decodeHead n).isSome
def OriginalRow (n : Nat) : Row := ((decodeTerm n).isSome,(decodeArgs n).isSome)
def ExactTermArgsTable : Prop := ∀ n, table n = (List.range n).map OriginalRow
def ExactTermArgsGuards : Prop := ∀ n, syntaxBits n = OriginalRow n

end LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmTargets
