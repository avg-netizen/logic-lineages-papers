module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomain
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL numeric arrow-type code, with no decoding or re-encoding of contexts. -/
def arrowCode (domain codomain : Nat) : Nat := 1 + Nat.pair domain codomain

def arrowValue (v : List.Vector Nat 2) : Nat := arrowCode (v.get 0) (v.get 1)

/-- Exactly the valid-window, typed function, typed argument and same-Gamma
checks on the first five original inputs. No output variable occurs here. -/
def active (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Prop :=
  GuardCalibration.validWindow n (v.get 0) = 1 ∧
  JointGammaTyped.typedValue n arity
    (List.Vector.ofFn ![v.get 0,arrowCode (v.get 1) (v.get 2),v.get 3]) = 1 ∧
  JointGammaTyped.typedValue n arity
    (List.Vector.ofFn ![v.get 0,v.get 1,v.get 4]) = 1 ∧
  JointGammaDomain.guardValue (List.Vector.ofFn ![v.get 3,v.get 4]) = 1

instance activeDecidable (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) :
    Decidable (active n arity v) := by
  unfold active
  infer_instance

def activationValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  if active n arity v then 1 else 0

/-- A literal composition/conjunction AST, preserving exact-one acceptance. -/
def activation (window : Program 1) (typed : Program 3) (guard arrow : Program 2) : Program 5 :=
  InternalAcceptance.conjunction
    (.composition window (fun _ => .projection 0))
    (InternalAcceptance.conjunction
      (.composition typed ![.projection 0,
        .composition arrow ![.projection 1,.projection 2],.projection 3])
      (InternalAcceptance.conjunction
        (.composition typed ![.projection 0,.projection 1,.projection 4])
        (.composition guard ![.projection 3,.projection 4])))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomain
