module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentCounterBoundDefinitions
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ExistentialPlan PrimitiveLowering ForwardTranslation
open RawSourceDAG (Code encode variableIndex)
open RawSourceDAG.InputCompiler (InputCode)
open CurrentDecisionEmitter

abbrev QueryCode := Bool × Code × Code
abbrev ArithmeticCode := Nat × InputCode
abbrev Extension (Γ : List Ty) := List.replicate 6 Ty.ground ++ Γ

def place (right : Bool) {Γ : List Ty} : Renaming (.ground::.ground::Γ) (Extension Γ)
  | _, .here => if right then fresh 2 else fresh 0
  | _, .there .here => if right then fresh 3 else fresh 1
  | _, .there (.there x) => shift 6 x

def probes (right : Bool) {Γ τ} (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ) :
    Input (Extension Γ) .ground × Input (Extension Γ) .ground :=
  (ScopedDAG.renameInput (place right) (AbsoluteProbeDAG.originalInput d),
    ScopedDAG.renameInput (place right) (AbsoluteProbeDAG.closedInput hg d))

def probeCodes (right : Bool) (d : Code) : Code × Code :=
  let ctx2 := 0 :: 0 :: d.1
  let ctx6 := List.replicate 6 0 ++ d.1
  let table := (if right then [2,3] else [0,1]) ++ RawSourceDAG.BinaryPlanCompiler.prefixTable 6 d.1
  let left := CurrentProbeCode.probeRaw (liftCode 2 d) 0
  let closed := CurrentProbeCode.probeRaw
    (RawSourceDAG.Operations.renameCode ctx2 [] (CurrentProbeCode.closeRaw d)) 1
  (RawSourceDAG.Operations.renameCode ctx6 table left,
    RawSourceDAG.Operations.renameCode ctx6 table closed)

def factorCode (d : Code) : Nat := 2*(SyntaxCode.typeLevel d.2.2.2+1)+1

noncomputable def counterCode (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : QueryCode) : InputCode :=
  let L := probeCodes false q.2.1
  let R := probeCodes true q.2.2
  let a := factorCode q.2.1
  let b := factorCode q.2.2
  let A := CurrentAbsolute.anchor p f q.2.1
  let B := CurrentAbsolute.anchor p f q.2.2
  let l := a+5
  let r := b+5
  let code := rowCodes q.1 (a+4+r,a+3+r,2+r,r) (b+4,b+3,2,0) (4+l+r) (5+l+r)
  (observeSteps L.1 L.2 0 1 4 a A ++
    observeSteps (liftCode l R.1) (liftCode l R.2) (2+l) (3+l) (5+l) b B ++ code.1, code.2)

def compiledPositive (p : AdmissibleSum.Policy) (d : Code) : List Nat :=
  ((PolicySourceInterface.compile p d.1.length (CurrentTreeCode.expand d)).getD (0,[])).2.map encodedClosedPositive

def positiveTest (p : AdmissibleSum.Policy) (q : QueryCode) : Bool :=
  positiveComparison (compiledPositive p q.2.1) (compiledPositive p q.2.2)

noncomputable def toArithmetic (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : QueryCode) : ArithmeticCode :=
  (q.2.1.1.length+6,
    if positiveTest p q then counterCode p f q else CurrentAttainment.truthCode)

def counterProgram (strict : Bool) {Γ σ τ} (hg : ∀ t ∈ Γ, t = Ty.ground)
    (a : Input Γ σ) (b : Input Γ τ) (leftAnchor rightAnchor : Nat) :
    InputNormalization.Input (Extension Γ) 0 :=
  let L := probes false hg a
  let R := probes true hg b
  let lv := fresh (Γ := Γ) (n := 6) 4
  let rv := fresh (Γ := Γ) (n := 6) 5
  observe L.1 L.2 (fresh 0) (fresh 1) lv (AbsoluteObserver.factor σ) leftAnchor
    (fun r l => observe (ScopedDAG.renameInput r R.1) (ScopedDAG.renameInput r R.2)
      (r (fresh 2)) (r (fresh 3)) (r rv) (AbsoluteObserver.factor τ) rightAnchor
      (fun s b => finalRows strict (mapPorts s l) b (s (r lv)) (s (r rv))))

def trueProgram (Γ : List Ty) : InputNormalization.Input Γ 0 :=
  .boolean (.eq .zero .zero) (.finish 0)

noncomputable def Universal (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool) {Γ σ τ}
    (a : Input Γ σ) (b : Input Γ τ) : Prop :=
  ∃ (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment p a.term = some av ∧
    AdmissibleAssignment.assignment p b.term = some bv ∧
    ∀ ρ : Variable Γ .ground → Nat,
      CurrentCounterBound.compareAt f strict av bv (fun c => inputs ρ c+1)

noncomputable def Ground (p : AdmissibleSum.Policy) (f : Nat → Nat) (strict : Bool) {Γ}
    (a b : Input Γ .ground) : Prop :=
  if strict then PolicyProgramComparisonTargets.Strict p f a.term b.term
  else PolicyProgramComparisonTargets.Weak p f a.term b.term

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
