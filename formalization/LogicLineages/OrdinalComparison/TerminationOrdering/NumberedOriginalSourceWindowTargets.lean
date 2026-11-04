module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowTargets
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedOriginalSourcePresentation
open NumberedOriginalSourceWindow NumberedOriginalSourcePresentationProof

def ActualTypeSubexpressionsPrimitive : Prop := Primrec Ty.subtypes

def ActualLiteralWindowCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (tau : Ty) (s : Term Symbol arity Gamma tau),
  termWindow tau (termCode (translateOriginal s))=Source.SourcePortContexts.literalTypes s

def ActualAllRequestsPrimitive : Prop := ∀ n : Nat, Primrec (@requestValue n)

def ActualFixedSourceWindowPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty),
  Primrec (Source.SourcePortContexts.literalTypes : Term (Fin n) arity Gamma tau → List Ty)

def ActualPackedSourceWindowPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun s : PackedSource (Fin n) arity Gamma => Source.SourcePortContexts.literalTypes s.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceWindowTargets
