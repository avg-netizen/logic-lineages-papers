module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionTargets
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliarySubstitution NumberedDirectCertificate

def ActualCodeSubstitutionPrimitive : Prop := ∀ n : Nat,
  Primrec (fun p : List (Code (Fin n)) × Code (Fin n) => substituteCode p.1 p.2)

def ActualTypedSubstitutionCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau)
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
  termCode (substitute q rho)=substituteCode (substitutionCodes Gamma rho) (termCode q)

def ActualArgumentSubstitutionCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta types : List Ty) (args : AuxArguments Symbol arity Gamma types)
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
  argumentsCode (substituteArguments args rho)=substituteCode (substitutionCodes Gamma rho) (argumentsCode args)

def ActualSingleEnvironmentCalibration : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (sigma : Ty) (a : AuxTerm Symbol arity Gamma sigma),
  substitutionCodes (sigma::Gamma) (singleSubstitution a)=termCode a :: (List.range Gamma.length).map Code.var

def ActualAllBetaCodePrimitive : Prop := ∀ n : Nat,Primrec₂ (@betaCode (Fin n))

def ActualBetaCodeCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma),
  betaCode Gamma.length (termCode q.2)=(directTarget arity Gamma .beta q).map (fun r => termCode r.2)

def ActualPackedBetaPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (directTarget arity Gamma .beta)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliarySubstitutionTargets
