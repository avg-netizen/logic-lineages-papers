module
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxQueryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalInput
open ForwardTranslation OrdinalSyntax

/-- The genuine literal-source frontend: typed raw T assignment, refusing
vector extraction, then literal scalar/positive AST query construction. -/
def compileSyntax (q : Query) : Option EncodedQuery := do
  let av ← DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.1
  let bv ← DefaultSourceAssignment.assignmentCode (List.replicate q.1 0) q.2.2.2
  let ac ← compileVectorCode av
  let bc ← compileVectorCode bv
  pure (q.2.1, ac, bc)

/-- Explicit true weak comparison, independent of every supplied coordinate. -/
def trueQuery : EncodedQuery := (false, (4, []), (4, []))

/-- Preserve original arity even on malformed input. The fallback extends
undefined raw syntax by true; it is not an extra premise on genuine terms. -/
def frontend (n : Nat) : Nat :=
  let q := decode n
  Encodable.encode (q.1, ((compileSyntax q).map normalizeQuerySyntaxCode).getD trueQuery)
end LogicLineages.OrdinalComparison.Source.OriginalInput
