module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotation

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicAnnotation
open GorbowSyntax GorbowNameDictionary GorbowRevisionComposition
open LogicLineages.ComputabilityKnowledge.GorbowAtomicAnnotation

def UniqueCalibration : Prop := ∀ n m (names : Fin n → Fin m),
  uniqueNames (namesList names)=true ↔ Function.Injective names

def CoverCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  coversNames m (GorbowFormulaPrefixCode.encode R) (namesList names)=true ↔ Covers R names

def ExactDomain : Prop := ∀ m raw ns, valid m raw ns=true ↔
  ∃ R : Formula m, ∃ names : Fin ns.length → Fin m,
    raw=GorbowFormulaPrefixCode.encode R ∧ ns=namesList names ∧
    Function.Injective names ∧ Covers R names ∧ AtomicMinus R

def OriginalCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  Function.Injective names → Covers R names → AtomicMinus R →
  valid m (GorbowFormulaPrefixCode.encode R) (namesList names)=true

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × List Nat => boundedNames p.1 p.2) ∧ Primrec uniqueNames ∧
  Primrec (fun p : Nat × List Nat × List Nat => coversNames p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => valid p.1 p.2.1 p.2.2)

def Target : Prop := UniqueCalibration ∧ CoverCalibration ∧ ExactDomain ∧ OriginalCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicAnnotation
