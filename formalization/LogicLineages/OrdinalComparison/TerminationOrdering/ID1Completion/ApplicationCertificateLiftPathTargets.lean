module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPathCertificates ApplicationCertificateLiftPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualLength : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context domain codomain argument : Nat) (entries : List EdgeEntry),
  (liftEntries n arity Gamma context domain codomain argument entries).length = entries.length

def ActualPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat), Primrec (pathValue n arity)

def ActualProgramWitness : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ p : Program 5,
    ∀ v, evaluate p v = pathValue n arity v

def ActualPathLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
    SubtypeClosed (fun t => t ∈ ctx.1.2) →
  ∀ (Gamma : List Ty) (sigma tau : Ty) (context : Nat),
    Encodable.decode context = some ctx →
  ∀ (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (entries : List EdgeEntry),
    InUniverse ctx.1.1 ctx.1.2 f → InUniverse ctx.1.1 ctx.1.2 g → InUniverse ctx.1.1 ctx.1.2 a →
    representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩ =
      packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma) →
    pathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩) entries = true →
    pathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app f a⟩)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app g a⟩)
      (liftEntries n arity Gamma context (typeNumber sigma) (typeNumber tau)
        (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)) entries) = true

def ActualPositiveLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
    SubtypeClosed (fun t => t ∈ ctx.1.2) →
  ∀ (Gamma : List Ty) (sigma tau : Ty) (context : Nat),
    Encodable.decode context = some ctx →
  ∀ (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (certificate : Nat),
    InUniverse ctx.1.1 ctx.1.2 f → InUniverse ctx.1.1 ctx.1.2 g → InUniverse ctx.1.1 ctx.1.2 a →
    representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩ =
      packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma) →
    positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,f⟩)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,g⟩) certificate = true →
    positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app f a⟩)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.app g a⟩)
      (liftPath n arity Gamma context (typeNumber sigma) (typeNumber tau)
        (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)) certificate) = true

/-- All original natural inputs and the original positive certificate are
retained. Only the explicit total K transforms the certificate. -/
def ActualOriginalPositiveLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f g a certificate : Nat),
    ApplicationDomain.active n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) →
    ContextUniform.positiveValue n arity (List.Vector.ofFn ![context,f,g,certificate]) = 1 →
    ContextUniform.positiveValue n arity
      (List.Vector.ofFn ![context,
        ApplicationResultBuilder.resultValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a]),
        ApplicationResultBuilder.resultValue n arity (List.Vector.ofFn ![context,domain,codomain,g,a]),
        pathValue n arity (List.Vector.ofFn ![context,domain,codomain,a,certificate])]) = 1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathTargets
