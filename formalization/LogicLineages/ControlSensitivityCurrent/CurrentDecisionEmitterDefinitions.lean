module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan PrimitiveLowering
open RawSourceDAG (Code variableIndex)
open RawSourceDAG.InputCompiler (InputCode InputStep prependStep)
open CurrentAttainment (repeatAdd addSteps)

abbrev Ports (Γ : List Ty) :=
  Variable Γ .ground × Variable Γ .ground × Variable Γ .ground × Variable Γ .ground
abbrev Indices := Nat × Nat × Nat × Nat

def liftCode (n : Nat) (c : Code) : Code :=
  RawSourceDAG.Operations.renameCode (List.replicate n 0 ++ c.1)
    (RawSourceDAG.BinaryPlanCompiler.prefixTable n c.1) c

def observe {Γ : List Ty} (a b : Input Γ .ground)
    (x y v : Variable Γ .ground) (factor anchor : Nat)
    (k : ∀ {Δ}, Renaming Γ Δ → Ports Δ → InputNormalization.Input Δ 0) :
    InputNormalization.Input Γ 0 :=
  .observation a
    (.observation (ScopedDAG.renameInput (Renaming.weaken Γ .ground) b)
      (.add (.var (.there (.there x))) .zero
        (repeatAdd (.there (.there (.there v))) .here factor (fun r sum =>
          .literal (factor * anchor)
            (.add (.var .here) (.var (.there (r (.there (.there (.there y))))))
              (k (fun z => .there (.there (r (.there (.there (.there z))))))
                (.there (.there (r (.there (.there .here)))),
                  .there (.there (r (.there .here))),
                  .there (.there sum), .here)))))))

def observeSteps (a b : Code) (x y v factor anchor : Nat) : List InputStep :=
  [((8,0,0),some a),((8,0,0),some (liftCode 1 b)),((6,x+3,0),none)] ++
    addSteps factor (v+3) ++
    [((7,factor*anchor,0),none),((6,1,y+(factor+5)),none)]

def finalRows {Γ : List Ty} (strict : Bool) (a b : Ports Γ) (v w : Variable Γ .ground) :
    InputNormalization.Input Γ 0 :=
  .boolean (.eq (.var a.1) (.var a.2.1))
    (.boolean (.eq (.var a.2.2.1) (.var a.2.2.2))
      (.boolean (.eq (.var b.1) (.var b.2.1))
        (.boolean (.eq (.var b.2.2.1) (.var b.2.2.2))
          (.boolean (if strict then .le (.var w) (.var v) else .lt (.var w) (.var v))
            (.boolean (.conj 3 4)
              (.boolean (.conj 2 3)
                (.boolean (.conj 0 1)
                  (.boolean (.conj 0 3) (.finish 0)))))))))

def rowCodes (strict : Bool) (a b : Indices) (v w : Nat) : InputCode :=
  ([((0,a.1+1,a.2.1+1),none),((0,a.2.2.1+1,a.2.2.2+1),none),
    ((0,b.1+1,b.2.1+1),none),((0,b.2.2.1+1,b.2.2.2+1),none),
    ((if strict then 1 else 2,w+1,v+1),none),
    ((4,3,4),none),((4,2,3),none),((4,0,1),none),((4,0,3),none)],0)

def mapPorts {Γ Δ} (r : Renaming Γ Δ) (p : Ports Γ) : Ports Δ :=
  (r p.1,r p.2.1,r p.2.2.1,r p.2.2.2)
def portIndices {Γ} (p : Ports Γ) : Indices :=
  (variableIndex p.1,variableIndex p.2.1,variableIndex p.2.2.1,variableIndex p.2.2.2)

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter
