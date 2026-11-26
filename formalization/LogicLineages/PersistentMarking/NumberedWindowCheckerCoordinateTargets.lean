module
public import LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinates
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinateTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressCheckers (multisetDomain)
open NumberedWindowConcreteCheckers (positive direct)
open NumberedWindowCheckerCoordinates

/-- One choice of each original unary/ternary program serves every outer context. -/
def FourPresentationPrograms : Prop :=
  ∀ (xs : Entries) (s : Settings), ∃ (i j : Program 1) (pos repl : Program 3),
    (∀ c n, evaluate (domain i) (c ::ᵥ n ::ᵥ nil) = (scalar s n).toNat) ∧
    (∀ c n, evaluate (domain j) (c ::ᵥ n ::ᵥ nil) = (multisetDomain s n).toNat) ∧
    (∀ c a b w, evaluate (suppliedCertificate pos) (c ::ᵥ a ::ᵥ b ::ᵥ w ::ᵥ nil) =
      (positive xs s a w b).toNat) ∧
    (∀ c a b w, evaluate (suppliedCertificate repl) (c ::ᵥ a ::ᵥ b ::ᵥ w ::ᵥ nil) =
      (direct xs s a w b).toNat)
end LogicLineages.PersistentMarking.NumberedWindowCheckerCoordinateTargets
