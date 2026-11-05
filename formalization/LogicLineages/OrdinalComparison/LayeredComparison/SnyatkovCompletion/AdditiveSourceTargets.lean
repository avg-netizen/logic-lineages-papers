module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceTargets
open CommonLayerSyntax NormalForm

def PurelyLinearGeneratedRows : Prop := ∀ (t : BaseTerm),
  AdditiveSource.termTest t = true → ∀ (start : Nat) (row : Row),
    row ∈ SourceTermGraph.rows start t → ∀ a ∈ row.2,
      ∃ i : Nat, a.2 = Summand.variable i

def ActualAdmissibility : Prop := ∀ p : SourceFormula,
  AdditiveSource.test p = true → QuantifiedLinear.admissible (SourceRows.translate p) = true

def ActualQuantifierElimination : Prop := ∀ p : SourceFormula,
  AdditiveSource.test p = true → ∀ ν : Nat → Nat,
    (AdditiveSource.eliminate p).eval ν ↔ p.eval ν

def ExactOutputSupport : Prop := ∀ (p : SourceFormula) (i : Nat),
  i ∈ (AdditiveSource.eliminate p).variables ↔ i ∈ p.variables

def ExactDecisionDomain : Prop := ∀ p : SourceFormula,
  (AdditiveSource.decideClosed p).isSome = (AdditiveSource.test p && p.variables.isEmpty)

def ActualClosedDecision : Prop := ∀ p : SourceFormula,
  AdditiveSource.test p = true → p.variables = [] → ∀ (ν : Nat → Nat) (answer : Bool),
    AdditiveSource.decideClosed p = some answer ↔ (p.eval ν ↔ answer = true)

def LiteralCodeCalibration : Prop :=
  (∀ t : BaseTerm, AdditiveSource.Code.termTest t.encode = AdditiveSource.termTest t) ∧
  (∀ p : SourceFormula, AdditiveSource.Code.test p.encode = AdditiveSource.test p) ∧
  (∀ p : SourceFormula, AdditiveSource.Code.eliminate p.encode = (AdditiveSource.eliminate p).encode) ∧
  (∀ p : SourceFormula, AdditiveSource.Code.decideClosed p.encode = AdditiveSource.decideClosed p)

def ActualNumericPrograms : Prop :=
  Primrec AdditiveSource.Code.termTest ∧ Primrec AdditiveSource.Code.test ∧
    Primrec AdditiveSource.Code.eliminate ∧ Primrec AdditiveSource.Code.decideClosed

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceTargets
