module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportTargets
open Turing Turing.ToPartrec Turing.PartrecToTM2 PredictionCompilerSupport

def ExactLabelEnumeration : Prop :=
  ∀ q x : Λ', x ∈ labelList q ↔ x ∈ trStmts₁ q

def ExactBodyEnumeration : Prop :=
  ∀ (c : Code) (k : Cont') (x : Λ'), x ∈ bodyList c k ↔ x ∈ codeSupp' c k

def ExactContinuationEnumeration : Prop :=
  ∀ (k : Cont') (x : Λ'), x ∈ continuationList k ↔ x ∈ contSupp k

def ExactCompilerSupport : Prop :=
  ∀ (c : Code) (k : Cont'), (supportList c k).toFinset = codeSupp c k

def ActualCompilerClosure : Prop :=
  ∀ (c : Code) (k : Cont'),
    @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (supportList c k).toFinset

end LogicLineages.ComputabilityKnowledge.PredictionCompilerSupportTargets
