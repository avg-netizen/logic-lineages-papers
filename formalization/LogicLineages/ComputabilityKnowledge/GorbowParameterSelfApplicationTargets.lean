module

public import LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplicationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.Targets
open GorbowSyntax GorbowSortedSyntaxCode GorbowPRProgram

/-- Exact AST substitution: ONE open uniform formula has the required closed instances. -/
def LiteralCommutation : Prop :=
  ∀ (phi : Formula 2) (u : Nat),
    GorbowStandardInstances.instantiate (openSelf phi) (Term.numeral u) = closedSelf phi u

/-- Sorted code of the ACTUAL two-variable formula and retained numeric parameter. -/
def NumericCalibration : Prop :=
  ∀ (phi : Formula 2) (u : Nat),
    numeric (formulaCode phi) u = some (formulaCode (closedSelf phi u))

/-- Exact typed successful domain, not a numeric surrogate for syntax. -/
def NumericExact : Prop :=
  ∀ code u out,
    numeric code u = some out ↔
      ∃ phi : Formula 2, code = formulaCode phi ∧ out = formulaCode (closedSelf phi u)

/-- Both literal raw and sorted numeric algorithms are primitive recursive. -/
def UniformPrograms : Prop :=
  Primrec (fun x : List Nat × Nat => rawParameterSelf x.1 x.2) ∧
  Primrec (fun x : Nat × Nat => numeric x.1 x.2)

/-- Actual fixed arity-two program, totalized on all raw inputs, for later
source-preserving registry embedding. No internal correctness is assumed. -/
def ProgramWitness : Prop :=
  ∃ p : Program 2, ∀ code u,
    evaluate p (code ::ᵥ u ::ᵥ List.Vector.nil) = (numeric code u).getD 0

def Target : Prop := LiteralCommutation ∧ NumericCalibration ∧ NumericExact ∧
  UniformPrograms ∧ ProgramWitness
end LogicLineages.ComputabilityKnowledge.GorbowParameterSelfApplication.Targets
