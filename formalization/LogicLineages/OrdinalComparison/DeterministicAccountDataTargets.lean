module
public import LogicLineages.OrdinalComparison.DeterministicAccountDataDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DeterministicAccountData.Targets
open ScalarAnnotationData ScalarCarrierAccounting

def ExactDataAccounting : Prop := ∀ (k : Nat) (Γ : List Ty)
    (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here), Valid d →
  ∃ rs c labels, accountData d = some (rs,c) ∧
    List.Forall₂ Matches rs labels ∧ Account (erase d) labels c

/-- Raw source/vector records correspond in exact order, not only by value.
No syntactic uniqueness of otherwise valid semantic carriers is asserted. -/
def ExactRecordCertification : Prop := ∀ (Γ : List Ty) (rs : List (UnaryRecord Γ)) (labels : List Carrier),
  List.Forall₂ Matches rs labels →
  rs.length = labels.length ∧
  rs.map (fun r => unitValue (r.vector 1)) = labels.map Carrier.head ∧
  ∀ r ∈ rs, r.Assigned ∧ r.NoGround

/-- Every unchanged Expr has a deterministic original-source account, with
actual complete source assignment and proof-only labels matching its output. -/
def ActualSourceAccount : Prop := ∀ (k : Nat) (Γ : List Ty) (n : Nat)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n),
  ∃ u rs c labels, sourceAccount e = some (u,rs,c) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧
    List.Forall₂ Matches rs labels ∧ Account (u 0) labels c
end LogicLineages.OrdinalComparison.Source.DeterministicAccountData.Targets
