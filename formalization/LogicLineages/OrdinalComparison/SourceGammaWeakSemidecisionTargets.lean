module
public import LogicLineages.OrdinalComparison.SourceGammaWeakSemidecisionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision.Targets

def EncodedWitness : Prop := ∀ (b code k : Nat),
  test b code k=true ↔ ∃ xs : List Nat,
    Encodable.decode (α := List Nat) k=some xs ∧
    SourceGammaWeakCounterexample.counterexample b code xs=true

def ExactSearch : Prop := ∀ (b code : Nat),
  ((search b code).Dom ↔
    ¬SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code) ∧
  (∀ k : Nat, k ∈ search b code ↔
    test b code k=true ∧ ∀ j : Nat, j<k → test b code j=false)

def FixedSemidecision : Prop := ∀ b : Nat,
  Computable (fun p : Nat×Nat => test b p.1 p.2) ∧
  Partrec (search b) ∧
  REPred (fun code =>
    ¬SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code)

def UniversalNormalForm : Prop := ∀ b : Nat,
  ComputablePred (fun p : Nat×Nat => test b p.1 p.2=false) ∧
  (∀ code : Nat,
    SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b) code ↔
      ∀ k : Nat, test b code k=false)
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakSemidecision.Targets
