module

public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation PositiveArithmeticOperators PositiveArithmeticTransforms

/-- Carry fixed-window programs into the original presentation, retaining the
certificate as the middle input to the supplied program. -/
def data (pI pJ : Program 1) (pR pD : Program 3) : Data :=
  ⟨NumberedWindowCheckerCoordinates.domain pI, NumberedWindowCheckerCoordinates.domain pJ,
   NumberedWindowCheckerCoordinates.suppliedCertificate pR,
   NumberedWindowCheckerCoordinates.suppliedCertificate pD⟩

def DomainHolds (p : Program 1) (x : Nat) : Prop :=
  evaluate p (x ::ᵥ nil) = 1

def CertificateHolds (p : Program 3) (source destination : Nat) : Prop :=
  ∃ c, evaluate p (source ::ᵥ c ::ᵥ destination ::ᵥ nil) = 1

def TaggedSemantics : Prop :=
  ∀ (pI pJ : Program 1) (pR pD : Program 3) (context : Nat) (P : Nat → Prop) (x : Nat),
    (realize P (sourceBody (data pI pJ pR pD) context).formula ![tagNumber false x] ↔
      DomainHolds pI x ∧ ∀ y, CertificateHolds pR x y → P (tagNumber false y)) ∧
    (realize P (sourceBody (data pI pJ pR pD) context).formula ![tagNumber true x] ↔
      DomainHolds pJ x ∧ ∀ y, CertificateHolds pD x y → P (tagNumber true y))

def AllTermsSemantics : Prop :=
  ∀ (pI pJ : Program 1) (pR pD : Program 3) (context : Nat) (P : Nat → Prop),
    realize P (allTermsFormula (data pI pJ pR pD) context) Empty.elim ↔
      ∀ x, DomainHolds pI x → P (tagNumber false x)

end LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
