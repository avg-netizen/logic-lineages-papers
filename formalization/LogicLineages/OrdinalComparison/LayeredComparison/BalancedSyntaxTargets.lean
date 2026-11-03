module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntaxDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedKeyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Targets
/-- Actual whole finite certificate, with ONE original raw assignment and
literal positive/full-basis atom grammar. This is not a certificate assumption. -/
def ActualRawSupportDomination:Prop:=∀Γ:List Nat,∀C:Certificate Γ,genuineCertificate Γ C→
  ∀E:Syntax Γ,genuineExpression Γ E→∀ν:Nat→Nat,∀i∈rawVariables Γ C E,ν i≤value Γ C E ν
/-- Original raw rawVariables outside actual support remain unrestricted. -/
def ActualRawSupportStability:Prop:=∀Γ:List Nat,∀C:Certificate Γ,∀E:Syntax Γ,∀ν μ:Nat→Nat,
  (∀i∈rawVariables Γ C E,ν i=μ i)→value Γ C E ν=value Γ C E μ
/-- Every positive source pair has the EXACT signed heterogeneous row, entire
outside remainder, actual norm arguments and whole original shared basis. -/
def ActualComparisonRow:Prop:=∀k:Nat,∀Γ:List Nat,∀C:Certificate (k::Γ),∀E F:Upper k,
  ∀ν:Nat→Nat,BalancedRow.wellFormed (basisValues k Γ C ν) (comparisonRow E F)∧
    BalancedRow.value (basisValues k Γ C ν) (comparisonRow E F)=
      (value (k::Γ) C E ν:Int)-(value (k::Γ) C F ν:Int)
def ActualHeadValidity:Prop:=∀k:Nat,∀Γ:List Nat,∀E F:Upper k,
  genuineExpression (k::Γ) E→genuineExpression (k::Γ) F→
    BalancedRow.genuineHeads (comparisonRow E F)
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax.Targets
