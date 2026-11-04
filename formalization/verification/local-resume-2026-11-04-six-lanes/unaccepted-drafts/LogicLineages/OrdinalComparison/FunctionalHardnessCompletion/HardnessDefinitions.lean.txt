module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.UndecidabilityDefinitions
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
open OriginalDomain SourceCollisionCompletion SourceClasses

def packGroundQuery {Γ : List Ty} (a b : OriginalTerm Γ .ground) : Nat :=
  Encodable.encode (Γ.map SyntaxCode.typeCode, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b)

def GroundComparison {Γ : List Ty} (strict : Bool)
    (a b : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ) : Prop :=
  if strict then rawScalar (valuation ρ) a < rawScalar (valuation ρ) b
  else rawScalar (valuation ρ) a ≤ rawScalar (valuation ρ) b

abbrev GroundQuery := Σ Γ : List Ty, OriginalTerm Γ .ground × OriginalTerm Γ .ground
def queryCode (q : GroundQuery) : Nat := packGroundQuery q.2.1 q.2.2
def queryBounds (level : Nat) (q : GroundQuery) : Prop :=
  (∀ τ ∈ q.1, τ.level ≤ 1) ∧ InternalLevelBound level q.2.1 ∧ InternalLevelBound level q.2.2
def queryUniversal (strict : Bool) (q : GroundQuery) : Prop :=
  ∀ ρ : AdmissibleSubstitution q.1, GroundComparison strict q.2.1 q.2.2 ρ

/-- The exact level-two finite-query clause: one total computable list of
query codes; every code is an actual bounded source query; unsatisfiability
means every query has its universal comparison true. Empty systems and
malformed polynomial codes are covered by the same total map. -/
def FiniteQueryReduction (strict : Bool) : Prop :=
  ∃ reduce : Nat → List Nat, Computable reduce ∧ ∀ e : Nat,
    ∃ queries : List GroundQuery, queries.map queryCode = reduce e ∧
      (∀ q ∈ queries, queryBounds 2 q) ∧
      (¬encodedPolynomialSolvable e ↔ ∀ q ∈ queries, queryUniversal strict q)

/-- A total computable decision program is required to answer correctly on
every genuine source pair in the PRINTED domain, including arbitrary types
of level one, not just the unary names used by the reduction. Values on
malformed codes are unrestricted, as in an algorithm on valid source inputs. -/
def HasComparisonDecider (level : Nat) (strict : Bool) : Prop :=
  ∃ decideQuery : Nat → Bool, Computable decideQuery ∧
    ∀ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      (∀ τ ∈ Γ, τ.level ≤ 1) → InternalLevelBound level a → InternalLevelBound level b →
      (decideQuery (packGroundQuery a b) = true ↔
        ∀ ρ : AdmissibleSubstitution Γ, GroundComparison strict a b ρ)

/-- A single computable source query for EACH encoded polynomial-system
instance. It supplies actual ground sources and all printed bounds, and
handles malformed polynomial codes through their explicit unsatisfiability.
No undecidability premise, seed supplier or source-realizability field is
assumed in this proposition. -/
def SingleQueryReduction (strict : Bool) : Prop :=
  ∃ reduce : Nat → Nat, Computable reduce ∧ ∀ e : Nat,
    ∃ (Γ : List Ty) (a b : OriginalTerm Γ .ground),
      packGroundQuery a b = reduce e ∧ (∀ τ ∈ Γ, τ.level ≤ 1) ∧
      InternalLevelBound 3 a ∧ InternalLevelBound 3 b ∧
      (¬encodedPolynomialSolvable e ↔ ∀ ρ : AdmissibleSubstitution Γ, GroundComparison strict a b ρ)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
