module
public import LogicLineages.PermittedControl.GroundComparisonTargets
public import LogicLineages.PermittedControl.GroundComparisonPositiveTargets
public import LogicLineages.PermittedControl.GroundScalarCircuitTargets

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparisonReduction
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation Canonical)
open GroundComparisonPositive (positiveTest)
open GroundScalarCircuit (Counter)

/-- The shared input index of #261's syntax code. -/
def idx {Γ : List Ty} (x : OrdinalComponent Γ) : Nat := SourceTypedPorts.variableIndex x.2.1

/-- Counterexample tag of each relation (GroundScalarCircuit.Counter). -/
def tagOf : Relation → Nat
  | .weak => 0
  | .strict => 1
  | .equal => 2

def equalFlag : Relation → Bool
  | .equal => true
  | _ => false

/-- The comparison of two canonical assignments reduces to one raw
positive-coordinate test and the absence of one scalar counterexample at
positive shared inputs. The hypotheses are exactly the per-term clauses of
#261 `TypedImage`. -/
def ExactCanonicalReduction : Prop :=
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (va : OrdinalVector Γ τ.level) (vb : OrdinalVector Γ υ.level)
    (ca : CompiledVector (OrdinalComponent Γ) τ.level) (cb : CompiledVector (OrdinalComponent Γ) υ.level),
    AdmissibleAssignment.assignment p a = some va → AdmissibleAssignment.assignment p b = some vb →
    (∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
      vectorValueWith ctrl ca ρ j = ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) (va j)) →
    (∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
      vectorValueWith ctrl cb ρ j = ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) (vb j)) →
    ∀ rel : Relation,
      (Canonical ctrl p rel a b ↔
        positiveTest (equalFlag rel) ((List.ofFn ca.positive).map closedPositiveCode)
            ((List.ofFn cb.positive).map closedPositiveCode) = true ∧
          ¬ ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧
            Counter (tagOf rel) (scalarValueWith ctrl (fun x => ν (idx x)) ca.scalar)
              (scalarValueWith ctrl (fun x => ν (idx x)) cb.scalar))

end LogicLineages.PermittedControl.GroundComparisonReduction
