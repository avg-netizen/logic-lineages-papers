module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Targets
open PolynomialGraphCompletion WordLinearDecisionCompletion LevelTwoCounterexample
open Source Source.ForwardTranslation Source.SourceClasses

/-- This unconditional adapter includes every literal global word domain,
including the bad-sign row below an unused disjunct. -/
def ExactMatrixSemantics : Prop := ∀ (p : Pair.Package) (ν : Nat → Nat),
  (Formula.meaningful (matrix p) ν ∧ Formula.eval ν (matrix p)) ↔ Pair.Matrix p ν

/-- This is a new interface proof obligation, not an assumed supplier. -/
def EmittedPackageShape : Prop := ∀ (q : SourceCode.Input) (p : Pair.Package),
  Admission.compile q = some p →
  ∃ (flag : Bool) (a b : Expr),
    ValidExpr a ∧ ValidExpr b ∧ Fresh q.1 a ∧ Fresh q.1 b ∧
    p = Pair.package q.1 q.2.1 flag a b

def LiteralPackageMetadata : Prop := ∀ (n mode : Nat) (flag : Bool) (a b : Expr),
  ValidExpr a → ValidExpr b → Fresh n a → Fresh n b →
    PackageCertified (Pair.package n mode flag a b)

def EmittedPackageMetadata : Prop := ∀ (q : SourceCode.Input) (p : Pair.Package),
  Admission.compile q = some p → PackageCertified p

def ExactMatrixSyntax : Prop := ∀ p : Pair.Package, PackageCertified p →
  Formula.allowed p.1.1 (matrix p) ∧
  (∀ i ∈ (matrix p).variables, i ∈ p.2.1)

/-- The actual finite existential prefix closes the exact original raw names.
No auxiliary word value is made an independent unconstrained witness. -/
def ExactClosedPackage : Prop := ∀ p : Pair.Package, PackageCertified p →
  (Pair.Closed p ↔ ∃ ν : Nat → Nat,
    Formula.meaningful (matrix p) ν ∧ Formula.eval ν (matrix p))

def LiteralCodeCalibration : Prop := ∀ p : Pair.Package,
  Code.matrix p = Formula.encode (matrix p)

def ActualMatrixProgram : Prop := Primrec Code.matrix

def ActualPackageDecision : Prop := ∀ p : Pair.Package, PackageCertified p →
  (packageCounterexample p = true ↔ Pair.Closed p)

def ExactSourceDomain : Prop := ∀ q : SourceCode.Input,
  (decision q).isSome = Admission.accepts q ∧
  (Admission.accepts q = false → decision q = none ∧ solve q = false)

def ActualNumericPrograms : Prop :=
  Computable packageCounterexample ∧ Computable decision ∧ Computable solve

/-- Actual original canonical assignments, shared positive ground variables,
and every internal subterm/binder type. Modes retain the original WW convention.
No typing, assignment, level classifier or compilation-success oracle is supplied. -/
def ActualTypedDecision : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
  InternalLevelBound 2 a → InternalLevelBound 2 b → ∀ mode : Nat,
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    decision (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) =
      some (solve (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)) ∧
    (solve (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = true ↔
      ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
        SourceCode.sourceRelation mode av bv ρ)

/-- Entire original paper08 thm:leveltwo. One concrete uniform numerical solver
is a construction obligation, with no counterexample/graph/word-solver premise. -/
def FullInternalLevelTwoComparison : Prop :=
  ∃ solver : SourceCode.Input → Bool, Computable solver ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
  InternalLevelBound 2 a → InternalLevelBound 2 b → ∀ mode : Nat,
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
    (solver (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = true ↔
      ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
        SourceCode.sourceRelation mode av bv ρ)

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Targets
