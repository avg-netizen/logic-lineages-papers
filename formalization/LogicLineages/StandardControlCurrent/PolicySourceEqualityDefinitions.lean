module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
public import LogicLineages.OrdinalComparison.GroundSourceEqualityDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceEquality
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation

def compileSyntax (p : Policy) (d n m : Nat) : Option EncodedQuery := do
  let av ← PolicyAssignment.assignmentCode p (List.replicate d 0) n
  let bv ← PolicyAssignment.assignmentCode p (List.replicate d 0) m
  let ac ← compileVectorCode av
  let bc ← compileVectorCode bv
  pure (false,ac,bc)

/-- Normalize extracted query syntax, never the original source term or its
literal assignment. Malformed raw source inputs explicitly return false. -/
noncomputable def equalityCode (p : Policy) (d n m : Nat) : Bool :=
  ((compileSyntax p d n m).map
    (fun q => GroundSourceEquality.queryEqualityFlag (normalizeQuerySyntaxCode q))).getD false

noncomputable def vectorAt {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : OriginalDomain.AdmissibleSubstitution Γ) (j : Nat) : Ordinal :=
  if h : j<n+1 then OriginalDomain.expressionValue s (v ⟨j,h⟩) else 0
end LogicLineages.StandardControlCurrent.PolicySourceEquality
