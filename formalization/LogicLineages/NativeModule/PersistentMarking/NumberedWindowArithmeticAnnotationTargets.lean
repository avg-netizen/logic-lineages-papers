module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCode
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypingBits

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationTargets
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticHeadCode NumberedWindowTypingBits NumberedWindowAnnotationAlgorithm

def HeadDeclaration : Prop := ∀ n, headOutput n = (decodeHead n).map
  (fun f => (encodeTy f.result,f.arguments.map encodeTy))

def LiteralAnnotations : Prop :=
  (∀ q : NTerm, (annotations (encodeTerm q)).1 = encodeTy q.type) ∧
  (∀ qs : NArgs, (annotations (encodeArgs qs)).2 = (annotationList qs).map encodeTy)

def DecodedAnnotations : Prop := ∀ n, output n =
  ((decodeTerm n).map (fun q => encodeTy q.type),
   (decodeArgs n).map (fun qs => (annotationList qs).map encodeTy))
end LogicLineages.PersistentMarking.NumberedWindowArithmeticAnnotationTargets
