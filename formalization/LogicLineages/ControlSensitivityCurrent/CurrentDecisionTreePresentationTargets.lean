module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationTargets

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open OriginalInput (Query)
open GroundEquivalence CurrentDecisionTreePresentation
open RawSourceDAG.InputCompiler (encodeInput)

def CompileOriginalTrees : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
    ∀ (n : Nat) (strict : Bool) (σ τ : Ty)
      (a : OriginalTerm (List.replicate n Ty.ground) σ)
      (b : OriginalTerm (List.replicate n Ty.ground) τ),
      let q : Query := (n,strict,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
      let da := CurrentTreeInputCoverage.input a
      let db := CurrentTreeInputCoverage.input b
      toDAGs q = some (strict,RawSourceDAG.encode ⟨_,σ,da⟩,RawSourceDAG.encode ⟨_,τ,db⟩) ∧
      ∃ r : InputNormalization.Input (List.replicate (n+6) Ty.ground) 0,
        toArithmetic p f q = some (n+6,encodeInput r) ∧
        toGround p f q = some (CurrentCompiler.expected r) ∧
        (OriginalUniversal p f strict a b ↔ ¬ ∃ ρ, r.eval p f ρ Fin.elim0) ∧
        (let pr := InputNormalization.normalize .nil r
         (OriginalUniversal p f strict a b ↔
            CurrentDecision.Ground p f true (BooleanCompiler.strictPair pr).1 (BooleanCompiler.strictPair pr).2) ∧
         (OriginalUniversal p f strict a b ↔
            CurrentDecision.Ground p f false (BooleanCompiler.weakPair pr).1 (BooleanCompiler.weakPair pr).2))

def GroundInclusion : Prop :=
  ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool) (n : Nat)
    (a b : OriginalTerm (List.replicate n Ty.ground) .ground),
    OriginalUniversal p f strict a b ↔
      if strict then PolicyProgramComparisonTargets.Strict p f a b
      else PolicyProgramComparisonTargets.Weak p f a b

def RawRejection : Prop :=
  ∀ (q : Query),
    let malformed := SyntaxCode.check (rawContext q.1) q.2.2.1 = none ∨
      SyntaxCode.check (rawContext q.1) q.2.2.2 = none
    (toDAGs q = none ↔ malformed) ∧
    ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat),
      (toArithmetic p f q = none ↔ malformed) ∧
      (toGround p f q = none ↔ malformed)

def Effective : Prop :=
  Computable toDAGs ∧
  ∀ (p : AdmissibleSum.Policy), PolicyShape.Effective p →
    ∀ (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
      Computable (toArithmetic p f) ∧ Computable (toGround p f)

def Full : Prop := CompileOriginalTrees ∧ GroundInclusion ∧ RawRejection ∧ Effective

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentationTargets
