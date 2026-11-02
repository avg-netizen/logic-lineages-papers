module
public import LogicLineages.OrdinalComparison.NumericAccountDataDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericAccountData.Targets
open ScalarAnnotationData ScalarCarrierAccounting DeterministicAccountData

def ExactScalarSurplus : Prop := ∀ (Γ : List Ty) (σ : Ty) (q : OrdinalExpression (σ::Γ)),
  surplusData (OrdinalSyntax.typedCode q) = (ordinalHeadFree q,HeadFiniteSurplus.surplus q)

/-- Includes all typed invalid trees and every failure, not just valid success. -/
def ExactNumericAccounting : Prop := ∀ (k : Nat) (Γ : List Ty)
    (d : Tree k (Ty.curriedGround (k+1)::Γ) .here),
  accountCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode) (SourceAnnotationCode.code d) =
    (accountData d).map (fun p => (p.1.map recordCode,p.2))

def PrimitiveRecursiveAlgorithms : Prop := Primrec surplusCode ∧ Primrec₂ accountCode ∧ Primrec₂ sourceAccountCode

/-- Every unchanged source grammar input has a genuine complete assignment and
an ordered actual carrier account from the numeric canonical builder. -/
def ActualCanonicalSource : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1)::Γ) .here n),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1)::Γ) (Ty.curriedGround n).level)
    (rs : List (UnaryRecord (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ)))
    (c : Nat) (labels : List Carrier),
    sourceAccountCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (TrackedSource.erase e)) =
        some (OrdinalSyntax.vectorCode u,rs.map recordCode,c) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    List.Forall₂ Matches rs labels ∧ Account (u 0) labels c
end LogicLineages.OrdinalComparison.Source.NumericAccountData.Targets
