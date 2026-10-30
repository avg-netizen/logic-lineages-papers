module

public import LogicLineages.OrdinalComparison.WWCanonicalPrimeDefinitions

@[expose] public section
/-! Paper09's abstraction-free source frontier. This is the actual typed
original-T kernel and the paid prime/application clauses, rejecting every
lambda. It is not a repaired or assumed whole-source abstraction assignment.
The kernel's separate named/de-Bruijn correspondence remains distinct. -/
namespace LogicLineages.OrdinalComparison.Source

def applicativeOnly {Γ : List Ty} {τ : Ty} : OriginalTerm Γ τ → Bool
  | .var _ | .zeroC | .succC | .caseC _ | .recC _ => true
  | .app f a => applicativeOnly f && applicativeOnly a
  | .lam _ => false
  | .ranked s _ => nomatch s

def ordinalApplicativeAssignment {Γ : List Ty} {τ : Ty} :
    OriginalTerm Γ τ → Option (OrdinalVector Γ τ.level)
  | .var v => ordinalCanonicalPrime (.var v)
  | .zeroC => ordinalCanonicalPrime .zeroC
  | .succC => ordinalCanonicalPrime .succC
  | .caseC σ => ordinalCanonicalPrime (.caseC σ)
  | .recC σ => ordinalCanonicalPrime (.recC σ)
  | .app f a => do
      let vf ← ordinalApplicativeAssignment f
      let va ← ordinalApplicativeAssignment a
      pure (ordinalCanonicalApplication vf va)
  | .lam _ => none
  | .ranked s _ => nomatch s

def successorProbe {Γ : List Ty} (v : Variable Γ .ground) : OriginalTerm Γ .ground :=
  .app .succC (.var v)

end LogicLineages.OrdinalComparison.Source
