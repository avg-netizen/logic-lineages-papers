module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionTargets
open Source Source.SyntaxCode Source.SourceClasses

/-- Full literal support, including internal binder/subterm types, for an
arbitrary original context. Unused high-level context types do not matter. -/
def ActualInternalBound : Prop := ∀ (Γ : List Ty) (τ : Ty)
    (t : OriginalTerm Γ τ) (L : Nat),
  Admission.test L (Γ.map typeCode) (encodeTerm t) = true ↔ InternalLevelBound L t

def ExactTypedAdmission : Prop := ∀ (Γ : List Ty) (τ : Ty) (L n : Nat),
  Admission.typedAccepts ((L,Γ.map typeCode,n),typeCode τ) = true ↔
    ∃ t : OriginalTerm Γ τ, encodeTerm t = n ∧ InternalLevelBound L t

def ExactAnyTypeAdmission : Prop := ∀ (Γ : List Ty) (L n : Nat),
  Admission.test L (Γ.map typeCode) n = true ↔
    ∃ (τ : Ty) (t : OriginalTerm Γ τ), encodeTerm t = n ∧ InternalLevelBound L t

def MalformedRejection : Prop := ∀ (L : Nat) (Γ : List Nat) (n : Nat),
  check Γ n = none → Admission.test L Γ n = false

def ExactGroundClass : Prop := ∀ p : SourceCode.Input,
  Admission.accepts p = true ↔
    ∃ (τ υ : Ty) (a : OriginalTerm (List.replicate p.1 Ty.ground) τ)
      (b : OriginalTerm (List.replicate p.1 Ty.ground) υ),
      encodeTerm a = p.2.2.1 ∧ encodeTerm b = p.2.2.2 ∧
        InternalLevelBound 2 a ∧ InternalLevelBound 2 b

/-- Successful guarded compilation certifies original source membership.
There is no caller typing, level, assignment, or compiler-success premise. -/
def ExactGuardedDomain : Prop := ∀ p : SourceCode.Input,
  (Admission.compile p).isSome = Admission.accepts p ∧
    (Admission.accepts p = false → Admission.compile p = none) ∧
    (Admission.accepts p = true → Admission.compile p = SourceCode.compile p)

/-- Every emitted package is calibrated to actual original canonical sources.
This remains a counterexample reduction, not existential decision. -/
def EmittedSourceCounterexample : Prop := ∀ (q : SourceCode.Input) (p : Pair.Package),
  Admission.compile q = some p →
  ∃ (τ υ : Ty) (a : OriginalTerm (List.replicate q.1 Ty.ground) τ)
    (b : OriginalTerm (List.replicate q.1 Ty.ground) υ)
    (av : OrdinalVector (List.replicate q.1 Ty.ground) τ.level)
    (bv : OrdinalVector (List.replicate q.1 Ty.ground) υ.level),
    encodeTerm a = q.2.2.1 ∧ encodeTerm b = q.2.2.2 ∧
    InternalLevelBound 2 a ∧ InternalLevelBound 2 b ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    (Pair.Closed p ↔ ∃ ρ : OrdinalComponent (List.replicate q.1 Ty.ground) → Nat,
      (∀ c, 0 < ρ c) ∧ ¬SourceCode.sourceRelation q.2.1 av bv ρ)

def ActualNumericPrograms : Prop :=
  Primrec (fun p : Admission.Input => Admission.test p.1 p.2.1 p.2.2) ∧
  Primrec Admission.typedAccepts ∧ Primrec Admission.accepts ∧ Primrec Admission.compile
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionTargets
