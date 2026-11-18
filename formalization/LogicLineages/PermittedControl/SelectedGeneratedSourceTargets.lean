module
public import LogicLineages.PermittedControl.SelectedGeneratedSourceDefinitions
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedGeneratedSourceTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedGeneratedSource SelectedSourceDomain

def ClosedSound : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (t : OrdinalExpression Γ)
    (c : ClosedPositive), extractPositive t = some c →
    ∀ ρ : OrdinalComponent Γ → Ordinal,
      c.evaluate.1.repr = ParametricSourceSuccessor.denoteWith ctrl ρ t

def ScalarSound : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (t : OrdinalExpression Γ)
    (s : Scalar (OrdinalComponent Γ)), compileScalar t = some s →
    ∀ ρ : OrdinalComponent Γ → Nat,
      (scalarValueWith ctrl ρ s : Ordinal) =
        ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) t

def FixedHeads : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ c : ClosedPositive, 0 < c.evaluate.1.repr ∧ 0 < fixedHead c ∧
    Order.IsSuccLimit (fixedHead c) ∧ fixedHead c < epsilonZero ∧
    Computable (fun n : Nat => ParametricActualCollapse.collapseWith ctrl (fixedHead c + (n : Ordinal)))

/-- Actual finite circuits compute from positive shared input tuples, at every arity. -/
def CircuitComputable : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
    Computable (fun xs : List Nat => scalarValueWith ctrl (fun x => xs.getD (index x) 0 + 1) s)

/-- Literal compiler/evaluator construction, not a semantic choice or fixed-G circuit value. -/
def Programs : Prop :=
  (∀ p : Policy, StandardControlCurrent.PolicyShape.Effective p →
    Computable (fun x : Nat × Nat => StandardControlCurrent.PolicySourceInterface.compile p x.1 x.2)) ∧
  Primrec encodedClosedPositive

def TypedImage : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level),
    AdmissibleAssignment.assignment p t = some v ∧ compileVector v = some c ∧
    StandardControlCurrent.PolicySourceInterface.compile p Γ.length (SyntaxCode.encodeTerm t) =
      some (c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) ∧
    (∀ j : Fin (τ.level+1), 0 < j.val → ordinalExpressionVariables (v j) = [] ∧
      ∃ z : ClosedPositive, extractPositive (v j) = some z ∧ 0 < z.evaluate.1.repr ∧
        encodedClosedPositive (closedPositiveCode z) = rawNoteEncode z.evaluate.1 ∧
        ∀ ρ : OrdinalComponent Γ → Ordinal,
          ParametricSourceSuccessor.denoteWith ctrl ρ (v j) = z.evaluate.1.repr) ∧
    (∀ ρ : OrdinalComponent Γ → Nat, ∀ j,
      vectorValueWith ctrl c ρ j = ParametricSourceSuccessor.denoteWith ctrl (fun x => (ρ x : Ordinal)) (v j)) ∧
    (∀ ρ : OrdinalComponent Γ → Nat, (∀ x, 0 < ρ x) → 0 < scalarValueWith ctrl ρ c.scalar)

/-- Complete current Paper17 thm:generated-source; all original internal types,
binders and recursors. Optional DAG sharing is not required, input identity is exact. -/
def FullSelectedGeneratedSource : Prop := ClosedSound ∧ ScalarSound ∧ FixedHeads ∧
  CircuitComputable ∧ Programs ∧ TypedImage ∧
  StandardControlCurrent.PolicySourceInterfaceTargets.RawInterface

end LogicLineages.PermittedControl.SelectedGeneratedSourceTargets
