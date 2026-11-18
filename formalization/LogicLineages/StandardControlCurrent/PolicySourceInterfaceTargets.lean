module
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceInterfaceTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def Programs : Prop :=
  (∀ p : Policy, PolicyShape.Effective p →
    Computable (fun x : Nat × Nat => PolicySourceInterface.compile p x.1 x.2)) ∧
  Primrec encodedClosedPositive ∧
  Computable (fun x : Nat × List Nat => scalarSyntaxValue x.1 x.2)

def FixedHeads : Prop := ∀ c : ClosedPositive,
  0 < c.evaluate.1.repr ∧ 0 < fixedHead c ∧ Order.IsSuccLimit (fixedHead c) ∧ fixedHead c < epsilonZero ∧
  Computable (fun n : Nat => actualCollapse (fixedHead c+(n : Ordinal)))

/-- All internal/result types and recursors retained; every extraction success,
closed positive field and semantic correspondence is a conclusion. -/
def TypedInterface : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ, σ=Ty.ground) →
  ∀ (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level),
    AdmissibleAssignment.assignment p t=some v ∧ compileVector v=some c ∧
    PolicySourceInterface.compile p Γ.length (SyntaxCode.encodeTerm t)=
      some (c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)) ∧
    (∀ j : Fin (τ.level+1), 0<j.val →
      ordinalExpressionVariables (v j)=[] ∧
      ∃ z : ClosedPositive, extractPositive (v j)=some z ∧ 0<z.evaluate.1.repr ∧
        encodedClosedPositive (closedPositiveCode z)=rawNoteEncode z.evaluate.1 ∧
        ∀ s : AdmissibleSubstitution Γ, expressionValue s (v j)=z.evaluate.1.repr) ∧
    (∀ s : AdmissibleSubstitution Γ, ∃ ρ : OrdinalComponent Γ → Nat,
      (∀ x,0<ρ x) ∧ (∀ x, valuation s x=(ρ x : Ordinal)) ∧
      ∀ j, c.value ρ j=expressionValue s (v j)) ∧
    (∀ ρ : OrdinalComponent Γ → Nat, (∀ x,0<ρ x) →
      ∃ s : AdmissibleSubstitution Γ, (∀ x,valuation s x=(ρ x : Ordinal)) ∧
        ∀ j, c.value ρ j=expressionValue s (v j)) ∧
    (∀ xs : List Nat,
      scalarSyntaxValue (c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)).1 xs=
        c.scalar.value (fun x => xs.getD (SourceTypedPorts.variableIndex x.2.1) 0+1))

def RawInterface : Prop := ∀ (p : Policy) (d n : Nat) (out : EncodedVector),
  PolicySourceInterface.compile p d n=some out ↔
    ∃ (τ : Ty) (t : OriginalTerm (List.replicate d Ty.ground) τ)
      (v : OrdinalVector (List.replicate d Ty.ground) τ.level)
      (c : CompiledVector (OrdinalComponent (List.replicate d Ty.ground)) τ.level),
      SyntaxCode.encodeTerm t=n ∧ AdmissibleAssignment.assignment p t=some v ∧
      compileVector v=some c ∧ c.syntaxCode (fun x => SourceTypedPorts.variableIndex x.2.1)=out

/-- Complete current canonical forward interface, not a comparison theorem. -/
def Full : Prop := PolicySourceEqualityTargets.GroundDomain ∧ Programs ∧ FixedHeads ∧
  TypedInterface ∧ RawInterface
end LogicLineages.StandardControlCurrent.PolicySourceInterfaceTargets
