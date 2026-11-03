module
public import LogicLineages.OrdinalComparison.OriginalGroundCompilerCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Targets
open DeterministicAccountData ScalarCarrierAccounting OriginalDomain OriginalScaleFlatList OriginalGroundDataConstruction
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactRecordPackaging : Prop := ∀ (k : Nat) (Γ : List Ty)
    (rs : List (UnaryRecord (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ)))
    (hr : ∀ r ∈ rs,r.Assigned),
  packRecords (SyntaxCode.typeCode (Ty.curriedGround (k+1))) (rs.map NumericAccountData.recordCode) =
    (operators rs hr).map NumericUnaryChain.operatorCode

def PrimitiveRecursiveAlgorithms : Prop := Primrec₂ packRecords ∧
  Primrec (fun p : List Nat×Nat×Nat×Nat => compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The complete effective original-budget ground-binder construction. No
success, child construction, reserve, bound, chosen K or scaled-budget premise
is supplied: all come from the unchanged original active-ground grammar and
actual caller. The uniform raw compiler is separately proved PR. -/
def ActualOriginalCompiler : Prop := ∀ (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1)::Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))), TrackedSource.active P = true →
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1)::Γ) 0)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (b : Nat)
    (rs : List (UnaryRecord (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ)))
    (c : Nat) (hr : ∀ r ∈ rs,r.Assigned),
    NumericAccountData.sourceAccountCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (TrackedSource.erase P)) =
        some (OrdinalSyntax.vectorCode u,rs.map NumericAccountData.recordCode,c) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.lam (TrackedSource.erase P)) = some B ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some caller ∧
    b = OriginalSecondBudget.scalarSecond (u 0) ∧ 4 ≤ b ∧ 3*rs.length+4 ≤ c ∧
    AdmissibleAssignment.box OrdinalSyntax.defaultPolicy B caller (OriginalSecondBudget.boxSecond k) =
      B (OriginalSecondBudget.boxSecond k) ∧
    (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (B (OriginalSecondBudget.boxSecond k)) = (b : Ordinal)) ∧
    ∃ (vC : OrdinalVector Γ 1)
      (hSat : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate k C) = some vC),
      (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (vC 1) = denote ν (caller (UnaryCarrier.headIndex k))) ∧
      let inputs := paidList b (operators rs hr) (unaryInput Γ (UnaryCarrier.saturate k C) vC hSat)
      ∃ K : OrdinalVector (HeterogeneousUnaryAssembly.context inputs) 1,
        compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1)))
          (SyntaxCode.encodeTerm (TrackedSource.erase P)) (SyntaxCode.encodeTerm C) =
            some (((HeterogeneousUnaryAssembly.context inputs).map SyntaxCode.typeCode,
              SyntaxCode.encodeTerm (SourceUnaryChain.chainSource (HeterogeneousUnaryAssembly.terms inputs)),
              OrdinalSyntax.vectorCode K),b,gap b (operators rs hr) c) ∧
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
          (SourceUnaryChain.chainSource (HeterogeneousUnaryAssembly.terms inputs)) = some K ∧
        0 < gap b (operators rs hr) c ∧
        ∀ (ρ : Variable Γ .ground → Nat)
          (μ : Variable (HeterogeneousUnaryAssembly.context inputs) .ground → Nat),
          ordinalNaturalProduct (scale b : Ordinal)
            (ordinalNaturalSum (expressionValue (UnitObservation.substitution ρ) (B (boxFirst k)))
              (expressionValue (UnitObservation.substitution ρ) (caller (UnaryCarrier.headIndex k)))) =
            expressionValue (UnitObservation.substitution μ) (K 1) + (gap b (operators rs hr) c : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalGroundCompilerCode.Targets
