module

public import LogicLineages.PersistentMarking.NumberedWindowAddressCheckers
public import LogicLineages.PersistentMarking.NumberedWindowPositivePathProgramTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowAddressCheckers NumberedWindowScalarAlgorithm List.Vector
open NumberedWindowPositivePathAlgorithm (Step)
open NumberedWindowPositivePathProgramTargets (StepInput)

def UnaryChecker (f : Nat → Bool) : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = (f n).toNat

def CertificateChecker (f : Nat → Nat → Nat → Bool) : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ a c b,
  GorbowPRProgram.evaluate p (a ::ᵥ c ::ᵥ b ::ᵥ List.Vector.nil) = (f a c b).toNat

def BothDomains : Prop := ∀ s : Settings, UnaryChecker (scalar s) ∧ UnaryChecker (multisetDomain s)

def BothCertificates : Prop := ∀ (s : Settings) (step : Step),
  Primrec (fun p : StepInput => step p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) →
    CertificateChecker (positive s step) ∧ CertificateChecker (direct s step)
end LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramTargets
