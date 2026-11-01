module
public import LogicLineages.OrdinalComparison.SourceScalarMultivariateDefinitions
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality
open Source Source.ForwardTranslation

/-- Literal equality of the actual ordinal vectors, with the ORIGINAL zero
padding at every out-of-level coordinate. Not a compiler-output predicate. -/
noncomputable def SourceEqualityAt {Γ : List Ty} {n m : Nat}
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m) (ρ : OrdinalComponent Γ → Nat) : Prop :=
  ∀ j : Nat, sourceVectorAtValue a ρ j=sourceVectorAtValue b ρ j

/-- Closed positive-coordinate guards plus genuine multivariate scalar
identity. Its input is NORMALIZED query data, not extracted source syntax. -/
noncomputable def queryEqualityFlag (q : EncodedQuery) : Bool :=
  positiveComparison q.2.1.2 q.2.2.2 && positiveComparison q.2.2.2 q.2.1.2 &&
    encodedMultivariateIdentity q.2.1.1 q.2.2.1

/-- The actual existing original-T frontend, retaining its essential syntax
normalization phase AFTER assignment/extraction. Invalid inputs explicitly
return false; correctness quantifies every well-typed original source. -/
noncomputable def sourceEqualityCode (d n m : Nat) : Bool :=
  ((OriginalInput.compileSyntax (d,false,n,m)).map
    (fun q => queryEqualityFlag (normalizeQuerySyntaxCode q))).getD false

end LogicLineages.OrdinalComparison.GroundSourceEquality
