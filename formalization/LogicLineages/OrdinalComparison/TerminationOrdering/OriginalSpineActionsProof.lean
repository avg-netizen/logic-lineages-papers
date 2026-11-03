module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsProof
open Source Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions

theorem variableEquations : OriginalSpineActionsTargets.VariableEquations := by
  intro Symbol inst arity I Γ σ v M P ρ mask types τ args h
  refine ⟨rfl,?_,?_,?_⟩
  · intro he; simp only [variableScan,if_pos he]
  · intro hne hp; simp only [variableScan,if_neg hne,hp,ite_true]
  · intro hp; simp [variableScan,hp]

theorem variableEvaluationMonotone : OriginalSpineActionsTargets.VariableEvaluationMonotone := by
  intro Symbol inst arity I Γ σ v M N P ρ η hMN hρη
  exact hρη v

theorem variableEvaluationNatural : OriginalSpineActionsTargets.VariableEvaluationNatural := by
  intro Symbol inst arity I Γ σ v M P Q h ρ
  rfl

theorem applyWithMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} {σ : Ty} (a b : Value I σ P) (types : List Ty) (τ : Ty) (v w : Values I types P)
    (h : σ=arrows types τ) (hab : a ≤ b) (hvw : v ≤ w) : applyWith a types τ v h ≤ applyWith b types τ w h := by
  cases h
  exact FullListValueApplicationProof.jointMonotone Symbol inferInstance arity I types τ P a b v w hab hvw

theorem applyWithNatural {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P Q : World I} (hPQ : Extends P Q) {σ : Ty} (a : Value I σ P) (types : List Ty) (τ : Ty) (v : Values I types P)
    (h : σ=arrows types τ) : RecursiveNaturalDomains.weaken hPQ (applyWith a types τ v h)=
      applyWith (RecursiveNaturalDomains.weaken hPQ a) types τ (weakenValues hPQ v) h := by
  cases h
  exact FullListValueApplicationProof.restriction Symbol inferInstance arity I types τ P Q hPQ a v

theorem variableScanMonotone : OriginalSpineActionsTargets.VariableScanMonotone := by
  intro Symbol inst arity I Γ σ v M N P ρ η mask types τ args args' h hMN hρη ha
  by_cases he : types=[]
  · simp only [variableScan,if_pos he]
    exact applyWithMonotone (ρ v) (η v) types τ args args' h (hρη v) ha
  · simp only [variableScan,if_neg he]
    split
    · exact le_rfl
    · exact applyWithMonotone (ρ v) (η v) types τ args args' h (hρη v) ha

theorem variableScanNatural : OriginalSpineActionsTargets.VariableScanNatural := by
  intro Symbol inst arity I Γ σ v M P Q hPQ ρ mask types τ args h
  by_cases he : types=[]
  · simp only [variableScan,if_pos he]
    exact applyWithNatural hPQ (ρ v) types τ args h
  · simp only [variableScan,if_neg he]
    split
    · exact ExecutableDomainBottomProof.weakeningBottom Symbol inst arity I τ P Q hPQ
    · exact applyWithNatural hPQ (ρ v) types τ args h

def variableAction {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) : PairedAction I Γ σ where
  evaluate := variableEvaluate v
  scan := variableScan v
  evaluateMonotone := variableEvaluationMonotone Symbol inferInstance arity I Γ σ v
  evaluateNatural := variableEvaluationNatural Symbol inferInstance arity I Γ σ v
  scanMonotone := variableScanMonotone Symbol inferInstance arity I Γ σ v
  scanNatural := variableScanNatural Symbol inferInstance arity I Γ σ v
  scanEmpty := by
    intro M P ρ mask args
    simp only [variableScan,if_pos rfl,applyWith,applyFull,variableEvaluate]
    rfl

theorem actualVariableAction : OriginalSpineActionsTargets.ActualVariableAction := by
  intro Symbol inst arity I Γ σ v
  exact ⟨variableAction v,rfl,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalSpineActionsProof
