module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedAuxiliaryCoding
open NumberedRewriteSyntax NumberedRewriteReduction NumberedSelectCertificate NumberedSelfApplication

def ActualArrowsPrimitive : Prop := Primrec (fun p : List Ty × Ty => arrows p.1 p.2)

def ActualSelfEntriesPrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : SelfData (Fin n) × List Ty => selfEntries p.1 p.2)

def ActualSelfCodePrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : SelfData (Fin n) × List Ty => selfCode p.1 p.2)

def ActualTypedSelfArgumentsCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (k : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty),
  argumentsCode (selfArguments k f base extraTypes extras types)=
    selfCode (k,headCode f,argumentsCode base,extraTypes,argumentsCode extras) types ∧
  (argumentList (selfArguments k f base extraTypes extras types)).map packedCode=
    selfEntries (k,headCode f,argumentsCode base,extraTypes,argumentsCode extras) types

def ActualApplicationPrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : Code (Fin n) × List (Ty × Code (Fin n)) => applyCode p.1 p.2)

def ActualTypedApplicationCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty)
    (tau : Ty) (q : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types),
  termCode (applyArguments q args)=applyCode (termCode q) ((argumentList args).map packedCode)

def ActualAllSelectCodePrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : List Ty × Nat × Ty × Code (Fin n) => selectCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def ActualSelectCodeCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty)
    (index : Nat) (q : Packed (Fin n) arity Gamma),
  selectCode types index q.1 (termCode q.2)=(selectTarget arity Gamma types index q).map (fun r => termCode r.2)

def ActualPackedSelectPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun p : List Ty × Nat × Packed (Fin n) arity Gamma => selectTarget arity Gamma p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelfApplicationTargets
