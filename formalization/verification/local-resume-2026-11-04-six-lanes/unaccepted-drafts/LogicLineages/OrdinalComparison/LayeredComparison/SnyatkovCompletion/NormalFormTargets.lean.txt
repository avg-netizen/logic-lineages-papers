module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormTargets
open NormalForm

def ExactOriginalDomainCutoffs : Prop :=
  ∀ (s : Summand) (ν : Nat → Nat), s.meaningful ν ↔ s.domainCutoff ≤ ν s.name

def ActualSignedRowDecomposition : Prop :=
  ∀ (row : Row) (ν : Nat → Nat),
    rowValue row ν = ((positiveTerm row).value ν : Int) - ((negativeTerm row).value ν : Int)

/-- EVERY original occurrence contributes, even coefficient zero or cancelled. -/
def ExactOriginalRowDomains : Prop :=
  ∀ (row : Row) (ν : Nat → Nat), (domainFormula row).eval ν ↔ rowMeaningful row ν

def ActualAtomCompilation : Prop := ∀ (a : Atom) (ν : Nat → Nat), a.compile.eval ν ↔ a.eval ν
def ActualBooleanCompilation : Prop := ∀ (p : Formula) (ν : Nat → Nat), p.compile.eval ν ↔ p.eval ν
def ExactVariableMembership : Prop :=
  ∀ (p : Formula) (i : Nat), i ∈ p.compile.variables ↔ i ∈ p.variables

def LiteralCodeCalibration : Prop :=
  (∀ s : Summand, Code.itemTerm s.data = s.term.encode ∧ Code.itemCutoff s.data = s.domainCutoff) ∧
  (∀ row : Row, Code.part false (rowData row) = (positiveTerm row).encode ∧
    Code.part true (rowData row) = (negativeTerm row).encode ∧
    Code.domains (rowData row) = (domainFormula row).compile.encode) ∧
  (∀ p : Formula, Code.formula p.encode = p.compile.encode)

def ActualNumericPrograms : Prop :=
  Primrec Code.itemTerm ∧ Primrec Code.itemCutoff ∧
    Primrec₂ Code.part ∧ Primrec Code.domains ∧ Primrec Code.atom ∧ Computable Code.formula

/-- The actual source Theorem1 route, STILL UNPAID. This is a target, never
a source-normalization/QE oracle field or premise of the row proofs. -/
def EffectiveSourceExistentialNormalForm : Prop :=
  ∃ (normalize : SourceFormula → List Nat × Formula) (program : Nat → Nat),
    Computable program ∧
    (∀ p, program p.encode = Encodable.encode ((normalize p).1, (normalize p).2.encode)) ∧
    (∀ p ν, p.eval ν ↔ existsPrefix ν (normalize p).1 (normalize p).2) ∧
    (∀ p, (normalize p).1.Nodup ∧ ∀ i ∈ (normalize p).1, i ∉ p.variables) ∧
    (∀ p i, i ∈ (normalize p).2.variables → i ∈ p.variables ∨ i ∈ (normalize p).1)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormTargets
