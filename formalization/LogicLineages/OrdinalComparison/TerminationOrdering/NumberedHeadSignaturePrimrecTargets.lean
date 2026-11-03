module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecTargets
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedHeadCodecPrimrec

def ActualHeadResultPrimitive : Prop := ∀ n : Nat, Primrec (fun head : HeadCode (Fin n) => headResult (decodeHead head))

def ActualHeadArgumentsPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun head : HeadCode (Fin n) => headArguments arity (decodeHead head))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadSignaturePrimrecTargets
