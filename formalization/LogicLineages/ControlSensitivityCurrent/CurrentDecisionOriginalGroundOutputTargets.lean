module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutputDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutputTargets

open LogicLineages.OrdinalComparison.Source GroundEquivalence
open LogicLineages.StandardControlCurrent
open OriginalInput (Query)
open RawSourceDAG.InputCompiler (encodeInput)
open CurrentDecisionOriginalGroundOutput

def TypedReencoding : Prop :=
  ∀ (Γ : List Ty) (a b : Input Γ .ground) (strict : Bool),
    asTreeQuery strict (RawPlanComparisonTargets.encodeComparison (a,b)) = literal strict a b

def ArithmeticOutputs : Prop :=
  ∀ (n : Nat) (r : InputNormalization.Input (List.replicate n Ty.ground) 0),
    let pr := InputNormalization.normalize .nil r
    outputQueries (CurrentCompiler.compile (n,encodeInput r)) =
      (literal true (BooleanCompiler.strictPair pr).1 (BooleanCompiler.strictPair pr).2,
       literal false (BooleanCompiler.weakPair pr).1 (BooleanCompiler.weakPair pr).2)

def OriginalOutputs : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (n : Nat) (strict : Bool) (σ τ : Ty)
      (a : OriginalTerm (List.replicate n Ty.ground) σ)
      (b : OriginalTerm (List.replicate n Ty.ground) τ),
      let q : Query := (n,strict,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
      ∃ r : InputNormalization.Input (List.replicate (n+6) Ty.ground) 0,
        let pr := InputNormalization.normalize .nil r
        let sa := (BooleanCompiler.strictPair pr).1
        let sb := (BooleanCompiler.strictPair pr).2
        let wa := (BooleanCompiler.weakPair pr).1
        let wb := (BooleanCompiler.weakPair pr).2
        CurrentDecisionTreePresentation.toArithmetic p f q = some (n+6,encodeInput r) ∧
        toGroundTrees p f q = some (literal true sa sb,literal false wa wb) ∧
        (CurrentDecisionTreePresentation.OriginalUniversal p f strict a b ↔
          PolicyProgramComparisonTargets.Strict p f sa.term sb.term) ∧
        (CurrentDecisionTreePresentation.OriginalUniversal p f strict a b ↔
          PolicyProgramComparisonTargets.Weak p f wa.term wb.term)

def Effective : Prop :=
  Computable₂ asTreeQuery ∧ Computable outputQueries ∧
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    ∀ (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
      Computable (toGroundTrees p f)

def Full : Prop := TypedReencoding ∧ ArithmeticOutputs ∧ OriginalOutputs ∧ Effective
end LogicLineages.ControlSensitivityCurrent.CurrentDecisionOriginalGroundOutputTargets
