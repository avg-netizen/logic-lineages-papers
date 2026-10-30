module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicSchemaCode
open GorbowSyntax GorbowNameDictionary GorbowRevisionComposition GorbowAtomicTruth
open LogicLineages.ComputabilityKnowledge.GorbowAtomicSchemaCode

def BodyCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  bodyRaw m (GorbowFormulaPrefixCode.encode R) (namesList names)=
    some (GorbowFormulaPrefixCode.encode (atomicBody R names))

def OriginalCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  AtomicMinus R → Function.Injective names → Covers R names →
  compileRaw m (GorbowFormulaPrefixCode.encode R) (namesList names)=
    some (GorbowFormulaPrefixCode.encode (atomicAxiom R names))

def ExactRaw : Prop := ∀ m raw ns out, compileRaw m raw ns=some out ↔
  ∃ R : Formula m, ∃ names : Fin ns.length → Fin m,
    raw=GorbowFormulaPrefixCode.encode R ∧ ns=namesList names ∧ AtomicMinus R ∧
    Function.Injective names ∧ Covers R names ∧ out=GorbowFormulaPrefixCode.encode (atomicAxiom R names)

def ExactNumeric : Prop := ∀ m raw ns out, compileNumber m raw ns=some out ↔
  ∃ R : Formula m, ∃ names : Fin ns.length → Fin m,
    raw=GorbowFormulaPrefixCode.encode R ∧ ns=namesList names ∧ AtomicMinus R ∧
    Function.Injective names ∧ Covers R names ∧ out=GorbowSortedSyntaxCode.formulaCode (atomicAxiom R names)

def Rejection : Prop := ∀ m raw ns,
  (compileRaw m raw ns=none ↔ GorbowAtomicAnnotation.valid m raw ns=false) ∧
  (compileNumber m raw ns=none ↔ GorbowAtomicAnnotation.valid m raw ns=false)

def ActualSemantics : Prop := ∀ m raw ns out, compileNumber m raw ns=some out →
  ∃ σ : Sentence, out=GorbowSortedSyntaxCode.formulaCode σ ∧
    ∀ initial k, σ.realize (GorbowSortedRevision.stage GorbowAtomicRegistry.ground initial (k+1)) Fin.elim0

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × List Nat × List Nat => bodyRaw p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => compileRaw p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => compileNumber p.1 p.2.1 p.2.2)

def Target : Prop := BodyCalibration ∧ OriginalCalibration ∧ ExactRaw ∧ ExactNumeric ∧ Rejection ∧ ActualSemantics ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicSchemaCode
