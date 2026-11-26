module

public import LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowShiftTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonTargets
open NumberedWindowSingletonAlgorithm NumberedWindowSyntax NumberedWindowArithmeticTermCode

def ExactSingletonMatrix : Prop :=
  (∀ a depth bound offset Q, encodeTerm Q + offset ≤ bound →
    (computed (encodeTerm a) depth bound (encodeTerm Q) offset).1 =
      encodeTerm (substitute (.cons a .nil) (depth+offset) Q)) ∧
  (∀ a depth bound offset qs, encodeArgs qs + offset ≤ bound →
    (computed (encodeTerm a) depth bound (encodeArgs qs) offset).2 =
      encodeArgs (substituteArgs (.cons a .nil) (depth+offset) qs))

def ExactSingletonOutput : Prop := ∀ inserted depth n,
  output inserted depth n =
    ((decodeTerm inserted).bind (fun a =>
        (decodeTerm n).map (fun q => encodeTerm (substitute (.cons a .nil) depth q))),
      (decodeTerm inserted).bind (fun a =>
        (decodeArgs n).map (fun qs => encodeArgs (substituteArgs (.cons a .nil) depth qs))))

end LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonTargets
