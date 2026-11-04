module
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Targets

def EncodedWitness : Prop := ∀ (b code k : Nat),
  test b code k=true ↔ ∃ xs : List Nat,
    Encodable.decode (α := List Nat) k=some xs ∧
    SourceGammaCounterexample.counterexample b code xs=true

def ExactSearch : Prop := ∀ (b code : Nat),
  ((search b code).Dom ↔
    ¬SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code) ∧
  (∀ k : Nat, k ∈ search b code ↔
    test b code k=true ∧ ∀ j : Nat, j<k → test b code j=false)

def FixedSemidecision : Prop := ∀ b : Nat,
  Computable (fun p : Nat×Nat => test b p.1 p.2) ∧
  Partrec (search b) ∧
  REPred (fun code =>
    ¬SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code)

def UniversalNormalForm : Prop := ∀ b : Nat,
  ComputablePred (fun p : Nat×Nat => test b p.1 p.2=false) ∧
  (∀ code : Nat,
    SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code ↔
      ∀ k : Nat, test b code k=false)
end LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Targets
