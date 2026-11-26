module
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalInputDomainDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCounterBound

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open OriginalInput (Query context decode)
open ForwardTranslation

def tupleRaw {Γ : List Ty} (xs : List Nat) (c : OrdinalComponent Γ) : Nat :=
  xs.getD (SourceTypedPorts.variableIndex c.2.1) 0 + 1

noncomputable def coordinate (f : Nat → Nat) {Γ : List Ty} {m : Nat}
    (v : OrdinalVector Γ m) (ρ : OrdinalComponent Γ → Nat) (j : Nat) : Ordinal :=
  ParametricSourceSuccessor.denoteWith f (fun c => (ρ c : Ordinal)) (ordinalVectorAt v j)

noncomputable def compareAt (f : Nat → Nat) {Γ : List Ty} {m n : Nat} (strict : Bool)
    (a : OrdinalVector Γ m) (b : OrdinalVector Γ n) (ρ : OrdinalComponent Γ → Nat) : Prop :=
  (∀ j : Nat, coordinate f a ρ (j+1) ≤ coordinate f b ρ (j+1)) ∧
  if strict then coordinate f a ρ 0 < coordinate f b ρ 0
  else coordinate f a ρ 0 ≤ coordinate f b ρ 0

noncomputable def Point (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) (xs : List Nat) : Prop :=
  ∀ (τ υ : Ty) (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level),
    SyntaxCode.encodeTerm a = q.2.2.1 → SyntaxCode.encodeTerm b = q.2.2.2 →
    AdmissibleAssignment.assignment p a = some av → AdmissibleAssignment.assignment p b = some bv →
    compareAt f q.2.1 av bv (tupleRaw xs)

noncomputable def Good (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) : Prop :=
  ∀ (τ υ : Ty) (a : OriginalTerm (context q) τ) (b : OriginalTerm (context q) υ)
    (av : OrdinalVector (context q) τ.level) (bv : OrdinalVector (context q) υ.level),
    SyntaxCode.encodeTerm a = q.2.2.1 → SyntaxCode.encodeTerm b = q.2.2.2 →
    AdmissibleAssignment.assignment p a = some av → AdmissibleAssignment.assignment p b = some bv →
    ∀ ρ : OrdinalComponent (context q) → Nat, (∀ c, 0 < ρ c) → compareAt f q.2.1 av bv ρ

noncomputable def codedGood (p : AdmissibleSum.Policy) (f : Nat → Nat) (n : Nat) : Prop :=
  Good p f (decode n)

noncomputable def CoordinateBound (p : AdmissibleSum.Policy) (f : Nat → Nat) : Prop :=
  ∃ b : Nat → Nat, Computable b ∧ ∀ n, ¬ codedGood p f n →
    ∃ xs : List Nat, xs.length = (decode n).1 ∧
      (∀ x ∈ xs, x+1 ≤ b n) ∧ ¬ Point p f (decode n) xs

def tupleEnvironment (xs : List Nat) : List Nat :=
  SourceGroundComponentEnvironment.environment (xs.map Nat.succ)

noncomputable def evaluators (f : Nat → Nat) (env v : List Nat) : List Nat :=
  v.map (CurrentOrdinalEvaluation.evaluate f env)

def compareNotes (strict : Bool) (a b : List Nat) : Bool :=
  positiveComparison a.tail b.tail &&
    if strict then decide (rawComparisonCode (a.getD 0 0) (b.getD 0 0) = 0)
    else decide (rawComparisonCode (a.getD 0 0) (b.getD 0 0) ≤ 1)

def assignments (p : AdmissibleSum.Policy) (q : Query) : Option (List Nat × List Nat) := do
  let types := (context q).map SyntaxCode.typeCode
  let a ← PolicyAssignment.assignmentCode p types q.2.2.1
  let b ← PolicyAssignment.assignmentCode p types q.2.2.2
  pure (a,b)

noncomputable def test (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) (xs : List Nat) : Bool :=
  match assignments p q with
  | none => true
  | some (a,b) =>
    let env := tupleEnvironment xs
    compareNotes q.2.1 (evaluators f env a) (evaluators f env b)

end LogicLineages.ControlSensitivityCurrent.CurrentCounterBound
