module
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.Targets
open SourceGroundComponentEnvironment SourceMachineRawValuations

def PositiveCoverage : Prop :=
  (∀ (n : Nat) (xs : List Nat), xs.length=n → positive xs=true →
    PositiveRaw (rawValuation (Γ:=List.replicate n Ty.ground) xs)) ∧
  (∀ (n : Nat) (ν : OrdinalComponent (List.replicate n Ty.ground) → Nat),
    PositiveRaw ν → ∃ xs : List Nat, xs.length=n ∧ positive xs=true ∧
      ∀ c, rawValuation xs c=ν c)

def ExplicitFailures : Prop :=
  (∀ (b code : Nat) (xs : List Nat), SourceRestrictedSyntaxChecker.restrictedCode code=false →
    counterexample b code xs=true) ∧
  (∀ x : Option Nat, compareResults none x=false ∧ compareResults x none=false)

def FixedComputable : Prop := ∀ b : Nat,
  Computable (fun p : Nat × List Nat => counterexample b p.1 p.2)

def ExactCounterexample : Prop := ∀ (b code : Nat),
  (¬SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code) ↔
    ∃ xs : List Nat, counterexample b code xs=true
end LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.Targets
