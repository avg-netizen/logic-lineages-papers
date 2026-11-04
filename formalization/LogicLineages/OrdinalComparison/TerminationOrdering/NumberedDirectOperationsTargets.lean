module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsTargets
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction NumberedDirectCertificate
open NumberedDirectOperations

def ActualArgumentAppendPrimitive : Prop := ∀ n : Nat,Primrec₂ (@appendArgumentCode (Fin n))

def ActualTypedArgumentAppend : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma xs ys : List Ty)
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys),
  argumentsCode (appendArguments a b)=appendArgumentCode (argumentsCode a) (argumentsCode b)

def ActualRawOpeningPrimitive : Prop := ∀ n : Nat,Primrec (@openCode (Fin n))

def ActualTypedOpeningCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (k : Nat) (f : Source.SourceMarkedSyntax.Head Symbol) (sigma tau : Ty)
    (base : AuxArguments Symbol arity Gamma (Source.SourceMarkedSyntax.headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types),
  termCode (openNumbered k f sigma tau base types extras)=
    openCode (k,headCode f,sigma,tau,argumentsCode base,types,argumentsCode extras)

def ActualAllAbstractionCodePrimitive : Prop := ∀ n : Nat,Primrec (@abstractionCode (Fin n))

def ActualAbstractionCodeCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  abstractionCode (termCode q.2)=(directTarget arity Gamma .abstraction q).map (fun r => termCode r.2)

def ActualPackedPutPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun p : Nat × Packed (Fin n) arity Gamma => directTarget arity Gamma (.put p.1) p.2)

def ActualPackedAbstractionPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (directTarget arity Gamma .abstraction)

def ActualPackedBottomPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (directTarget arity Gamma .bottom)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsTargets
