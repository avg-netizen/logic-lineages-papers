module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationDefinitions
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence PrimitiveLowering ExistentialPlan
open RawSourceDAG.InputCompiler (InputCode InputStep)

abbrev Request := Nat × Nat × Nat × Nat
abbrev Unary := Input [] (.arrow .ground .ground)

def bound (c : Nat) (q : Request) : Nat :=
  max c (q.2.2.1 - 100) * q.1 + q.2.1 % q.1

def residue (q : Request) : Nat :=
  (q.2.2.2 + fastControlResidue q.2.2.1 + (q.2.2.1 - 1)) % q.2.2.1

noncomputable def AttainsAt (head : Ordinal) (q : Request) (t : Nat) : Prop :=
  actualOrdinalNorm head ≤ t ∧
    Nat.ModEq q.1 t q.2.1 ∧ Nat.ModEq q.2.2.1 (actualHeadCount head t) q.2.2.2

noncomputable def Attains (head : Ordinal) (q : Request) : Prop :=
  ∃ t : Nat, AttainsAt head q t

def digits (p : AdmissibleSum.Policy) (h : RawSourceDAG.Code) : List Nat :=
  (PolicyAssignment.assignmentCode p [] (CurrentTreeCode.expand h)).getD []

noncomputable def headCode (p : AdmissibleSum.Policy) (h : RawSourceDAG.Code) : Nat :=
  encodedNaturalProduct CurrentOrdinalEvaluation.omegaCode
    (CurrentOrdinalEvaluation.evaluate Phi [] ((digits p h).getD 1 0))

noncomputable def offset (p : AdmissibleSum.Policy) (h : RawSourceDAG.Code) : Nat :=
  rawNormCode (headCode p h) +
    encodedFiniteValue (CurrentOrdinalEvaluation.evaluate Phi [] ((digits p h).getD 0 0)) + 1

noncomputable def count (head t : Nat) : Nat := by
  classical
  exact (PermittedControl.terminalSearchWith Phi
    (encodedNaturalSum head (encodedNatNote (t - rawNormCode head)))).getOrElse 0

noncomputable def finitePrefix (head : Nat) (q : Request) (b : Nat) : Bool :=
  (List.range b).any (fun t => decide (rawNormCode head ≤ t ∧
    Nat.ModEq q.1 t q.2.1 ∧ Nat.ModEq q.2.2.1 (count head t) q.2.2.2))

/-- The continuation receives the actual embedding of the original names
and the current accumulator. -/
def repeatAdd {Γ : List Ty} (x : Variable Γ .ground) (a : Variable Γ .ground) :
    Nat → (∀ {Δ}, Renaming Γ Δ → Variable Δ .ground → InputNormalization.Input Δ 0) →
      InputNormalization.Input Γ 0
  | 0, k => k (fun y => y) a
  | n+1, k => .add (.var a) (.var x)
      (repeatAdd (.there x) .here n (fun r z => k (fun y => r (.there y)) z))

def tailProgram (h : Unary) (c : Nat) (q : Request) :
    InputNormalization.Input (List.replicate 2 Ty.ground) 0 :=
  .literal (bound c q - c)
    (repeatAdd (.there .here) .here q.1 (fun r a =>
      .unary h a (.literal (residue q)
        (repeatAdd (.there (.there (r (.there (.there .here))))) .here q.2.2.1
          (fun s b => .boolean (.eq (.var (s (.there .here))) (.var b)) (.finish 0))))))

def truthProgram : InputNormalization.Input (List.replicate 2 Ty.ground) 0 :=
  .boolean (.eq .zero .zero) (.finish 0)

def addSteps (n k : Nat) : List InputStep :=
  (List.range n).map (fun i => ((6,1,k+i+1),none))

def tailCode (h : RawSourceDAG.Code) (c : Nat) (q : Request) : InputCode :=
  ([((7,bound c q-c,0),none)] ++ addSteps q.1 1 ++
    [((9,0,0),some h),((7,residue q,0),none)] ++
    addSteps q.2.2.1 (q.1+4) ++ [((0,q.2.2.1+2,1),none)], 0)

def truthCode : InputCode := ([((0,0,0),none)],0)

noncomputable def select (head c : Nat) (h : RawSourceDAG.Code) (q : Request) : InputCode :=
  if finitePrefix head q (bound c q) then truthCode else tailCode h c q

noncomputable def run (p : AdmissibleSum.Policy) (x : RawSourceDAG.Code × Request) :
    RawSourceDAG.PlanComparison.OutputCode :=
  CurrentCompiler.compile (2, select (headCode p x.1) (offset p x.1) x.1 x.2)

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
