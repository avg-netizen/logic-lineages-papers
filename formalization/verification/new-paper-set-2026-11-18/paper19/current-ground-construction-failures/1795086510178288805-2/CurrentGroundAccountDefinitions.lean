module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationTargets
public import LogicLineages.OrdinalComparison.NumericAccountDataDefinitions
public import LogicLineages.OrdinalComparison.NumericUnaryChainDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent (PolicyAssignment)
open AdmissibleSum ScalarAnnotationData DeterministicAccountData
open SourceFreeOccurrences

/-- Proof-only certification of existing data. The algorithm does not choose
a carrier from this predicate or eliminate an existence proof. -/
def certify {Γ} {p : Policy} (r : UnaryRecord Γ)
    (ha : AdmissibleAssignment.assignment p r.source = some r.vector)
    (hn : r.NoGround) : CurrentReserve.Carrier p :=
  ⟨Γ,r.source,r.vector,ha,hn⟩

def Matches {Γ} {p : Policy} (r : UnaryRecord Γ) (a : CurrentReserve.Carrier p) : Prop :=
  ∃ (ha : AdmissibleAssignment.assignment p r.source = some r.vector) (hn : r.NoGround),
    a = certify r ha hn

/-- Build the exact actual carrier, retaining the scalar produced by p. -/
def carrierRecord (p : Policy) {k Γ}
    (op : Operator (Ty.curriedGround (k+1) :: Γ)) :
    Option (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)) := do
  let src := CurrentSelectedCarriers.carrierAt (.here : Variable _ _) op.arity op.source
  let vec ← AdmissibleAssignment.assignment p src
  pure ⟨src,vec⟩

/-- Deterministic accounting of literal ordered occurrences. Only the
generated positive finite-code evaluator classifies a selected head. -/
def accountData (p : Policy) {k Γ} (d : Tree k (Ty.curriedGround (k+1) :: Γ) .here) :
    Option (List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)) × Nat) :=
  if ordinalHeadFree (erase d) then some ([],1) else
  match d with
  | .free _ => none
  | .tracked => some ([],1)
  | .add a b => do
      let (xs,c) ← accountData p a
      let (ys,e) ← accountData p b
      pure (xs++ys,c+e+1)
  | .collapse op tail => do
      let (_,finite,value) ← UnitHeadCode.classify (OrdinalSyntax.typedCode op.head)
      let (xs,c) ← accountData p tail
      if finite then pure (xs,c+value+HeadFiniteSurplus.surplus op.head)
      else
        let r ← carrierRecord p op
        pure (xs++[r],c+HeadFiniteSurplus.surplus op.head)

def sourceData (p : Policy) {k Γ n}
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n) := do
  let (u,d) ← CurrentGroundAnnotation.build p e
  let (rs,c) ← accountData p d
  pure (u,rs,c)

def recordCode {k Γ} (r : UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)) :
    NumericUnaryChain.RawOperator :=
  let t := SyntaxCode.typeCode (Ty.curriedGround (k+1))
  ([t,t],SyntaxCode.encodeTerm r.source,OrdinalSyntax.vectorCode r.vector)

def carrierCode (p : Policy) (Γ : List Nat) (op : Nat) : Option NumericUnaryChain.RawOperator := do
  let σ := Γ.getD 0 0
  let Δ := σ :: Γ
  let r := SourceAnnotationCode.operatorArity op
  let src := GroundCaptureClosingCode.sourceCode Δ 0
    (NumericCarrierData.saturateSource r
      (SourceCarrierMapCode.mapCode true 0 (SourceAnnotationCode.operatorSource op)))
  let v ← PolicyAssignment.assignmentCode p Δ src
  pure ([σ,σ],src,v)

/-- Chosen-policy carrier compile replaces only the legacy carrier/vector
builder. Literal finite classification and scalar surplus remain the same. -/
def accountCode (p : Policy) (Γ : List Nat) : Nat → Option (List NumericUnaryChain.RawOperator × Nat)
  | n =>
    if OrdinalSyntax.headFree (SourceAnnotationCode.eraseCode 0 n) then some ([],1)
    else if n%4=0 then none
    else if n%4=1 then some ([],1)
    else if h : n%4=2 ∨ n%4=3 then
      have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
      let q := (n/4).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then do
        let (xs,c) ← accountCode p Γ q.1
        let (ys,e) ← accountCode p Γ q.2
        pure (xs++ys,c+e+1)
      else do
        let head := SourceAnnotationCode.operatorHead q.1
        let (_,finite,value) ← UnitHeadCode.classify head
        let (xs,c) ← accountCode p Γ q.2
        if finite then pure (xs,c+value+NumericAccountData.surplusCode head)
        else
          let r ← carrierCode p Γ q.1
          pure (xs++[r],c+NumericAccountData.surplusCode head)
    else none
termination_by n => n
decreasing_by all_goals assumption

def sourceCode (p : Policy) (Γ : List Nat) (src : Nat) :
    Option (List Nat × List NumericUnaryChain.RawOperator × Nat) := do
  let (u,d) ← CurrentGroundAnnotationCode.buildCode p Γ 0 src
  let (rs,c) ← accountCode p Γ d
  pure (u,rs,c)

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAccount
