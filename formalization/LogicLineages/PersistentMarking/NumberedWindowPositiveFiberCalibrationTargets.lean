module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberPrograms
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPositiveFiberPrograms (guarded)

def contextField (q : Nat) : Option Nat := (addressView q).map (fun a => pack a.1)

def resultField (q : Nat) : Option Nat := (addressView q).map (fun a => a.2.1)

def ContextProgram (p : Program 1) : Prop :=
  ∀ q, evaluate p (q ::ᵥ nil) = Encodable.encode (contextField q)

def ResultProgram (p : Program 1) : Prop :=
  ∀ q, evaluate p (q ::ᵥ nil) = Encodable.encode (resultField q)

def PositiveProgram (entries : Entries) (s : Settings) (r : Program 3) : Prop :=
  ∀ q w v, evaluate r (q ::ᵥ w ::ᵥ v ::ᵥ nil) = (positive entries s q w v).toNat

/-- Both actual address projections are available on all natural inputs,
including failed parses with their original optional-code representation. -/
def ProjectionPrograms : Prop := ∃ ctx ty : Program 1, ContextProgram ctx ∧ ResultProgram ty

/-- For any calibrated supplied checker, the literal guarded choice has
identical results on every triple, not only on admitted positive paths. -/
def SamePositiveChecker : Prop :=
  ∀ (entries : Entries) (s : Settings) (ctx ty : Program 1) (r : Program 3),
    ContextProgram ctx → ResultProgram ty → PositiveProgram entries s r →
    PositiveProgram entries s (guarded ctx ty r)

end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberCalibrationTargets
