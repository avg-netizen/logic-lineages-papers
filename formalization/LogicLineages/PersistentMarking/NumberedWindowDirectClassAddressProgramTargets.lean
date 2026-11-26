module

public import LogicLineages.PersistentMarking.NumberedWindowDirectClassAddress
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProgramTargets
open NumberedWindowAddressCheckersProgramTargets (CertificateChecker)
open NumberedWindowDirectClassAddress
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

def DirectClassAddressProgram : Prop :=
  ∀ positive : Nat → Nat → Nat → Bool,
    CertificateChecker positive → CertificateChecker (directAddress positive)

def ConcreteDirectClassAddressProgram : Prop :=
  ∀ (entries : Entries) (s : Settings),
    CertificateChecker (directAddress (NumberedWindowConcreteCheckers.positive entries s))

end LogicLineages.PersistentMarking.NumberedWindowDirectClassAddressProgramTargets
