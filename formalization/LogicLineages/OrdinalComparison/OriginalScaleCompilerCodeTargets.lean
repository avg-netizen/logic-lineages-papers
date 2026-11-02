module
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Targets
open HeterogeneousUnaryAssembly OriginalScaleFlatList OriginalDomain NumericUnaryChain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactCallerCode : Prop := ∀ (k : Nat) (Γ : List Ty)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (k+1)).level),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some u →
  callerCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1))) (SyntaxCode.encodeTerm C) =
    some ([],SyntaxCode.encodeTerm (UnaryCarrier.saturate k C),
      OrdinalSyntax.vectorCode (DeterministicCarrierData.saturateVector k u))

def ExactPaidList : Prop := ∀ (Γ : List Ty) (b : Nat) (xs : List (Operator Γ)) (caller : Operator Γ) (c : Nat),
  paidCode b (xs.map operatorCode) (operatorCode caller) = (paidList b xs caller).map operatorCode ∧
  gapCode b (xs.map operatorCode) c = gap b xs c

def PrimitiveRecursiveAlgorithms : Prop :=
  Primrec (fun p : List Nat×Nat×Nat => callerCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×List RawOperator×RawOperator => paidCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×List RawOperator×Nat => gapCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : List Nat×Nat×Nat×Nat×List RawOperator => compileScaleCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- Given actual records and a paid reserve, produce the literal actual K at
the ORIGINAL scale2^b, with full vector and strict finite gap. The eventual
canonical P compiler must derive both numerical premises, not assume them. -/
def ActualScaledCompiler : Prop := ∀ (k : Nat) (Γ : List Ty)
    (xs : List (Operator Γ)) (C : OriginalTerm Γ (Ty.curriedGround (k+1))) (b c : Nat),
  4 ≤ b → 3*xs.length+4 ≤ c →
  ∃ (uC : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (vC : OrdinalVector Γ 1)
    (hC : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some uC)
    (hSat : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate k C) = some vC),
    (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (vC 1) = denote ν (uC (UnaryCarrier.headIndex k))) ∧
    let inputs := paidList b xs (unaryInput Γ (UnaryCarrier.saturate k C) vC hSat)
    ∃ K : OrdinalVector (context inputs) 1,
      compileScaleCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1)))
        (SyntaxCode.encodeTerm C) b (xs.map operatorCode) =
          some ((context inputs).map SyntaxCode.typeCode,
            SyntaxCode.encodeTerm (SourceUnaryChain.chainSource (terms inputs)),OrdinalSyntax.vectorCode K) ∧
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (SourceUnaryChain.chainSource (terms inputs)) = some K ∧
      0 < gapCode b (xs.map operatorCode) c ∧
      ∀ (ρ : Variable Γ .ground → Nat) (μ : Variable (context inputs) .ground → Nat),
        ordinalNaturalProduct (scale b : Ordinal)
          (ordinalNaturalSum (sourceSum xs + (c : Ordinal))
            (expressionValue (UnitObservation.substitution ρ) (uC (UnaryCarrier.headIndex k)))) =
          expressionValue (UnitObservation.substitution μ) (K 1) + (gapCode b (xs.map operatorCode) c : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Targets
