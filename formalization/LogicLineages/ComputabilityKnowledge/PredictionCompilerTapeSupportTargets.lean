module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportTargets
open Turing Turing.ToPartrec Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport

open scoped Classical in
def ExactStackStatementEnumeration : Prop :=
  ∀ (q : StackStatement) (l : TapeLabel), l ∈ stackStatementList q ↔ l ∈ TM2to1.trStmts₁ q

open scoped Classical in
def ExactTapeLabelEnumeration : Prop :=
  ∀ (c : Code) (k : Cont'),
    (tapeLabels c k).toFinset = TM2to1.trSupp tr (codeSupp c k)

open scoped Classical in
def ExactTapeStatementEnumeration : Prop :=
  ∀ (q : TapeStatement) (r : TapeStatement), r ∈ tapeStatementList q ↔ r ∈ TM1.stmts₁ q

open scoped Classical in
def ExactPostLabelEnumeration : Prop :=
  ∀ (c : Code) (k : Cont'),
    (postLabels c k).toFinset = TM1to0.trStmts tapeMachine (tapeLabels c k).toFinset

open scoped Classical in
def ActualTapeCompilerClosure : Prop :=
  ∀ (c : Code) (k : Cont'),
    letI : Inhabited Λ' := ⟨trNormal c k⟩
    TM1.Supports tapeMachine (tapeLabels c k).toFinset

open scoped Classical in
def ActualPostCompilerClosure : Prop :=
  ∀ (c : Code) (k : Cont'),
    letI : Inhabited Λ' := ⟨trNormal c k⟩
    TM0.Supports postMachine {l | l ∈ postLabels c k}

end LogicLineages.ComputabilityKnowledge.PredictionCompilerTapeSupportTargets
