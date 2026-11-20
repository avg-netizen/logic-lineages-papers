module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPresentationTargets
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowComputabilityFormulaTargets (accepts)

def RawDomain {α : Type} (p : Program 1) (x : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph p (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![x]

def DomainRules : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (odd : Bool) (c : Nat)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x : OrdinaryArithmetic.Term α),
    (Nonempty (Derivation body Γ (carrier (data i j r d) odd c x))) ↔
    Nonempty (Derivation body Γ (RawDomain (if odd then j else i) x))

def CertificateRules : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (odd : Bool) (c : Nat)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (x y w : OrdinaryArithmetic.Term α),
    (Nonempty (Derivation body Γ (certificate (data i j r d) odd c x y w))) ↔
    Nonempty (Derivation body Γ (accepts (if odd then d else r) x w y))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateTargets
