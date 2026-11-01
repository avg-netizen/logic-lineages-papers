module
public import LogicLineages.OrdinalComparison.ComparisonTreeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualNumericComparisonChildWellFounded : Prop := WellFounded ComparisonNumericChild

def ActualComparisonFrontierProgram : Prop := Primrec encodedComparisonFrontierStep ∧
  Primrec₂ encodedComparisonFrontier ∧ ∀ root : Nat × Nat,
    encodedComparisonFrontier root 0=[root] ∧ ∀ k,
      encodedComparisonFrontier root (k+1)=encodedComparisonFrontierStep (encodedComparisonFrontier root k)

def ActualComparisonFrontierTerminates : Prop :=
  ∀ root : Nat × Nat, ∃ depth : Nat, encodedComparisonFrontier root depth=[]

/-- Genuinely total all-code least-depth search, including invalid source
inputs. Actual program closure, source relation well-foundedness, all domains,
Computable realization and exact minimal empty frontier are conclusions. -/
def ActualComparisonDepthProgram : Prop := Partrec encodedComparisonDepthPartial ∧
  (∀ root : Nat × Nat,(encodedComparisonDepthPartial root).Dom) ∧
  Computable encodedComparisonTreeDepth ∧ ∀ root : Nat × Nat,
    1≤encodedComparisonTreeDepth root ∧
    encodedComparisonFrontier root (encodedComparisonTreeDepth root)=[] ∧
    ∀ k<encodedComparisonTreeDepth root,encodedComparisonFrontier root k≠[]

def ActualComparisonTreeLayersProgram : Prop := Computable encodedComparisonTreeLayers ∧
  ∀ root : Nat × Nat,
    (encodedComparisonTreeLayers root).length=encodedComparisonTreeDepth root+1 ∧
    (encodedComparisonTreeLayers root).getD 0 []=[root] ∧
    (encodedComparisonTreeLayers root).getD (encodedComparisonTreeDepth root) []=[] ∧
    ∀ k<encodedComparisonTreeDepth root,
      (encodedComparisonTreeLayers root).getD (k+1) []=
        encodedComparisonFrontierStep ((encodedComparisonTreeLayers root).getD k [])

def FullActualFiniteComparisonTree : Prop := ActualNumericComparisonChildWellFounded ∧
  ActualComparisonFrontierProgram ∧ ActualComparisonFrontierTerminates ∧
  ActualComparisonDepthProgram ∧ ActualComparisonTreeLayersProgram

end LogicLineages.OrdinalComparison.Targets
