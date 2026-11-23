module
public import LogicLineages.PermittedControl.GroundComparisonMainTargets
public import LogicLineages.PermittedControl.PolicySuppliedCodeMacroInterpreterTargets
public import LogicLineages.PermittedControl.SelectedFiniteQueryTargets
public import LogicLineages.PermittedControl.SelectedSingleQueryTargets

@[expose] public section
namespace LogicLineages.PermittedControl.UniformGroundComparison
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain
open GroundComparison (Relation Canonical)
open PolicySuppliedCodeMacro (RealizesPolicy)

/-- Runtime input of the uniform procedure: the supplied policy program,
the context length and the two literal term codes. -/
abbrev GroundArgs := Nat.Partrec.Code × Nat × Nat × Nat

/-- The same with the near-control parameter `b` as a runtime input. -/
abbrev NearArgs := Nat × GroundArgs

/-- For one control: ONE partial recursive procedure per relation, taking
the policy program as an input. The existential over the procedure is
outside the quantifier over policies. On every program realizing a policy
it halts on every raw input, and on the codes of typed terms whose free
variables all have ground type its answer is the truth value of the
canonical comparison under that policy. Nothing is asked on programs that
realize no policy; the procedure may diverge there. -/
def UniformGroundDecidable (ctrl : Nat → Nat) : Prop :=
  ∀ rel : Relation, ∃ decide : GroundArgs →. Bool, Partrec decide ∧
    ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
      (∀ n ca cb : Nat, (decide (e,n,ca,cb)).Dom) ∧
      ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
        ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
          ∃ answer : Bool,
            decide (e,Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = Part.some answer ∧
            (answer = true ↔ Canonical ctrl p rel a b)

/-- The near controls jointly: one procedure per relation taking the
parameter `b` together with the policy program and the query. -/
def UniformNearGroundDecidable : Prop :=
  ∀ rel : Relation, ∃ decide : NearArgs →. Bool, Partrec decide ∧
    ∀ (bound : Nat) (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
      (∀ n ca cb : Nat, (decide (bound,e,n,ca,cb)).Dom) ∧
      ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
        ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
          ∃ answer : Bool,
            decide (bound,e,Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) =
              Part.some answer ∧
            (answer = true ↔ Canonical (nearControl bound) p rel a b)

/-- Clause (i) of Paper 17 `thm:main` with the printed uniformity: in the
supplied policy program at the factorial control, and jointly in the
supplied `b` and the policy program at the near controls. -/
def UniformGroundComparison : Prop :=
  UniformGroundDecidable factorialControl ∧ UniformNearGroundDecidable

/-- The uniform statement is at least as strong as the per-policy
comparator `GroundComparison` of #1428. -/
def UniformImpliesGround : Prop :=
  UniformGroundComparison → GroundComparison.GroundComparison

/-- Strengthened comparator for Paper 17 `thm:main`. Beyond #1429's
`MainComparison` it asks clause (i) uniformly (above), and for clauses
(ii)–(iii) it exposes the reductions as the literal policy- and
control-independent programs they are: the finite-query and single-query
reduction codes are primitive recursive and are exact total reductions at
every selected control and every policy. -/
def UniformMainComparison : Prop :=
  Targets.FullControl ∧ Targets.NearControlModular ∧ UniformGroundComparison ∧
    SelectedFunctionalHardnessTargets.SelectedFunctionalHardness ∧
    SelectedFiniteQueryTargets.LiteralProgram ∧ SelectedFiniteQueryTargets.ExactTotalReduction ∧
    SelectedSingleQueryTargets.LiteralPrograms ∧ SelectedSingleQueryTargets.ExactTotalReduction

end LogicLineages.PermittedControl.UniformGroundComparison
