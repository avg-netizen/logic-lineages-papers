module
public import LogicLineages.ControlSensitivityCurrent.CurrentUnitEliminationTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluationDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeDefinitions
public import LogicLineages.OrdinalComparison.UnitHeadCodeDefinitions
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.HeadEndpointDefinitions
public import LogicLineages.OrdinalComparison.EncodedFiniteTailDefinitions
public import LogicLineages.PermittedControl.CollapseTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleAssignment AdmissibleSum ForwardTranslation
open CurrentUnitElimination (groundCtx WireCtx shift)

/-- The two first fields really exist: the caller has positive level and
its original arrow has level at least two. These are not zero-filled fields. -/
def callerFirst (σ : Ty) (h : 0 < σ.level) : Fin (σ.level+1) := ⟨1, by omega⟩
def sourceFirst (σ τ : Ty) : Fin ((Ty.arrow σ τ).level+1) :=
  ⟨1, by change 1 < max (σ.level+1) τ.level+1; omega⟩
def boxSecond (σ τ : Ty) (h : 0 < σ.level) : Fin ((Ty.arrow σ τ).level+1) :=
  ⟨2, by change 2 < max (σ.level+1) τ.level+1; omega⟩

noncomputable def atUnits (f : Nat → Nat) {Γ} (a : OrdinalExpression Γ) : Ordinal :=
  ParametricSourceSuccessor.denoteWith f (fun _ => 1) a

/-- Arbitrary actually assigned B,C,K paying the same printed premise. B
and C have exactly the same original context; K may have its own context.
The unopened full original box, not the truncated application or any
modified copy, supplies b. Finite Δ includes zero and b has no floor. -/
structure Paid (p : Policy) (f : Nat → Nat) {Γ Ξ : List Ty} {σ τ : Ty}
    (B : OriginalTerm Γ (.arrow σ τ)) (C : OriginalTerm Γ σ)
    (K : OriginalTerm Ξ (Ty.curriedGround 1)) (b Δ : Nat) : Type where
  callerLevel : 0 < σ.level
  Bvector : OrdinalVector Γ (Ty.arrow σ τ).level
  Cvector : OrdinalVector Γ σ.level
  Kvector : OrdinalVector Ξ 1
  assignB : assignment p B = some Bvector
  assignC : assignment p C = some Cvector
  assignK : assignment p K = some Kvector
  budget : atUnits f (box p Bvector Cvector (boxSecond σ τ callerLevel)) = (b : Ordinal)
  payment : ordinalNaturalProduct ((2^b : Nat) : Ordinal)
    (ordinalNaturalSum (atUnits f (Bvector (sourceFirst σ τ)))
      (atUnits f (Cvector (callerFirst σ callerLevel)))) =
    atUnits f (Kvector 1) + (Δ : Ordinal)

noncomputable def Paid.paidHead {p f Γ Ξ σ τ B C K b Δ}
    (h : @Paid p f Γ Ξ σ τ B C K b Δ) : Ordinal :=
  ordinalNaturalProduct Ordinal.omega0
    (ordinalNaturalProduct ((2^b : Nat) : Ordinal)
      (ordinalNaturalSum (atUnits f (h.Bvector (sourceFirst σ τ)))
        (atUnits f (h.Cvector (callerFirst σ h.callerLevel)))))

noncomputable def Paid.baseHead {p f Γ Ξ σ τ B C K b Δ}
    (h : @Paid p f Γ Ξ σ τ B C K b Δ) : Ordinal :=
  ordinalNaturalProduct Ordinal.omega0 (atUnits f (h.Kvector 1))

/-- Ordinary finite ordinal tail, after an explicit separate genuine guard. -/
noncomputable def J (f : Nat → Nat) (ξ : Ordinal) (t : Nat) : Nat :=
  ParametricActualCollapse.collapseWith f (actualHeadInitial ξ t)
noncomputable def shiftHead (β : Ordinal) (j : Nat) : Ordinal :=
  β + Ordinal.omega0 * (j : Ordinal)
noncomputable def RayBase (β : Ordinal) (c : Nat) : Nat := actualOrdinalNorm β+c+1

/-- Increasing rank of each exact ground identity, skipping functional slots. -/
def groundRank : {Γ : List Ty} → Variable Γ .ground → Fin (groundCtx Γ).length
  | [],x => nomatch x
  | .ground :: _,.here => ⟨0,by simp [groundCtx]⟩
  | .ground :: _,.there x => (groundRank x).succ
  | .arrow _ _ :: Γ,.there x => @groundRank Γ x

def newGround (Γ : List Ty) : {n : Nat} → Fin n → Variable (WireCtx n Γ) .ground
  | 0,i => Fin.elim0 i
  | _+1,i => Fin.cases .here (fun j => .there (newGround Γ j)) i

abbrev FreshCtx (Γ : List Ty) := WireCtx (groundCtx Γ).length Γ

def freshRename (Γ : List Ty) : Renaming Γ (FreshCtx Γ)
  | .ground,x => newGround Γ (groundRank x)
  | .arrow _ _,x => shift (groundCtx Γ).length x

/-- Only this explicitly auxiliary source is renamed and zero-closed.
Fresh ground ports are in a disjoint prefix, and functional names are
merely embedded; no all-unit original inhabitant exists or is used. -/
def freshCopy {Γ τ} (K : OriginalTerm Γ τ) : OriginalTerm (FreshCtx Γ) τ :=
  K.rename (freshRename Γ)
def zeroCopy {Γ τ} (K : OriginalTerm Γ τ) : OriginalTerm (FreshCtx Γ) τ :=
  UnaryCarrier.closeGround (freshCopy K)
def raySource {Γ} (K : OriginalTerm Γ (Ty.curriedGround 1)) :
    OriginalTerm (.ground :: FreshCtx Γ) .ground :=
  .app ((zeroCopy K).rename (fun x => .there x)) (.var .here)

/-- Original ground-port rank table is purely positional. Invalid entries
are deterministic; correctness never relies on a missing lookup. -/
def groundCount (Γ : List Nat) : Nat := (Γ.filter (· = 0)).length
def freshContext (Γ : List Nat) : List Nat := List.replicate (groundCount Γ) 0 ++ Γ
def freshTable (Γ : List Nat) : List Nat := (List.range Γ.length).map fun i =>
  if Γ.getD i 1 = 0 then groundCount (Γ.take i) else groundCount Γ + i

def auxiliaryCode (Γ : List Nat) (src : Nat) : Option (List Nat × Nat) := do
  let K ← CurrentTreeInputCoverage.compile Γ src
  let Ξ := freshContext Γ
  let R := RawSourceDAG.Operations.renameCode Ξ (freshTable Γ) K
  let closed := GroundCaptureClosingCode.sourceCode Ξ 0 (CurrentTreeCode.expand R)
  pure (0 :: Ξ,8*Nat.pair (ContextInsertionCode.sourceCode 0 1 closed) 0+5)

/-- Numeric normal-note heads/closed scalar. Every closed evaluation uses
literal code at the user's actual f; no caller-supplied numeric oracle. -/
abbrev ParameterCode := Nat × Nat × Nat

def shiftCode (β δ : Nat) : Nat :=
  encodedNaturalSum β (encodedNaturalProduct CurrentOrdinalEvaluation.omegaCode (encodedNatNote δ))

noncomputable def parameterCode (p : Policy) (f : Nat → Nat)
    (Γ : List Nat) (src δ : Nat) : Option ParameterCode := do
  if SyntaxCode.check Γ src = some (SyntaxCode.typeCode (Ty.curriedGround 1)) then
    let v ← PolicyAssignment.assignmentCode p Γ src
    let h ← v[1]?
    let z ← v[0]?
    let a ← UnitHeadCode.positiveCode h
    let β := encodedClosedHead a
    let c := encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f [] (UnitHeadCode.unitCode z))
    pure (β,shiftCode β δ,c)
  else none

noncomputable def valueCode (f : Nat → Nat) (ξ t : Nat) : Nat :=
  PermittedControl.evaluatorWith f (encodedFiniteTail ξ (t-rawNormCode ξ))

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
