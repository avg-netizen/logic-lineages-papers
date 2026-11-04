module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeTargets
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedOriginalSourceCodec NumberedOriginalSourceShape

def ActualTermShape : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (tau : Ty)
    (q : AuxTerm Symbol arity Gamma tau),(project q).isSome=codeShape (termCode q)

def ActualArgumentsShape : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty)
    (args : AuxArguments Symbol arity Gamma types),(projectArguments args).isSome=codeShape (argumentsCode args)

def ActualCodeShapePrimitive : Prop := ∀ n : Nat,Primrec (@codeShape (Fin n))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeTargets
