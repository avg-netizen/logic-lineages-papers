module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCounterexampleDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Targets

def ExplicitFailures : Prop :=
  (∀ (b code : Nat) (xs : List Nat), SourceRestrictedSyntaxChecker.restrictedCode code=false →
    counterexample b code xs=true) ∧
  (∀ x : Option Nat, compareResults none x=false ∧ compareResults x none=false) ∧
  (∀ left right : Nat, compareResults (some left) (some right)=true ↔ right<left)

def FixedComputable : Prop := ∀ b : Nat,
  Computable (fun p : Nat × List Nat => counterexample b p.1 p.2)

def ExactCounterexample : Prop := ∀ (b code : Nat),
  (¬SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code) ↔
    ∃ xs : List Nat, counterexample b code xs=true
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Targets
