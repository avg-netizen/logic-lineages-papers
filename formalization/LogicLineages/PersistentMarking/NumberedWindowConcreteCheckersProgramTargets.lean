module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers
public import LogicLineages.PersistentMarking.NumberedWindowAddressCheckersProgramTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramTargets
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowAddressCheckersProgramTargets (UnaryChecker CertificateChecker)
open NumberedWindowAddressCheckers (multisetDomain)
open NumberedWindowConcreteCheckers (positive direct)

def AllFourProgramWitnesses : Prop := ∀ (entries : Entries) (s : Settings),
  UnaryChecker (scalar s) ∧ UnaryChecker (multisetDomain s) ∧
  CertificateChecker (positive entries s) ∧ CertificateChecker (direct entries s)
end LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramTargets
