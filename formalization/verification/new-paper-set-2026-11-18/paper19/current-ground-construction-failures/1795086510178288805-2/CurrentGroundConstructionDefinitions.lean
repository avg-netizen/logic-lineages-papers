module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountTargets
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction

open LogicLineages.OrdinalComparison (ordinalNaturalSum ordinalNaturalProduct)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent (PolicyAssignment)
open AdmissibleSum SourceTypedPorts DeterministicAccountData

/-- A private prefix belongs to one occurrence; the suffix Γ is shared by
every input. Source syntax and the complete vector are unmodified payloads. -/
structure Operator (Γ : List Ty) where
  privateContext : List Ty
  term : OriginalTerm (privateContext ++ Γ) (Ty.curriedGround 1)
  vector : OrdinalVector (privateContext ++ Γ) 1

def Operator.Assigned {Γ} (p : Policy) (op : Operator Γ) : Prop :=
  AdmissibleAssignment.assignment p op.term = some op.vector

def context {Γ : List Ty} : List (Operator Γ) → List Ty
  | [] => Γ
  | op::ops => op.privateContext ++ context ops

def baseMap {Γ : List Ty} : (ops : List (Operator Γ)) → Renaming Γ (context ops)
  | [] => fun x => x
  | op::ops => fun x => shiftVariable op.privateContext (baseMap ops x)

def headMap {Γ : List Ty} (op : Operator Γ) (ops : List (Operator Γ)) :
    Renaming (op.privateContext ++ Γ) (context (op::ops)) :=
  HeterogeneousUnaryAssembly.prefixLift (baseMap ops) op.privateContext

/-- One occurrence-by-occurrence, literal simultaneous renaming. No sharing
of private slots, deduplication, change of original Γ or scalar reset. -/
def merged {Γ : List Ty} : (ops : List (Operator Γ)) →
    List (OriginalTerm (context ops) (Ty.curriedGround 1) × OrdinalVector (context ops) 1)
  | [] => []
  | op::ops =>
    (op.term.rename (headMap op ops), SourceRenaming.renameVector (headMap op ops) op.vector) ::
      (merged ops).map (fun pr => (pr.1.rename (shiftVariable op.privateContext),
        SourceRenaming.renameVector (shiftVariable op.privateContext) pr.2))

def terms {Γ : List Ty} (ops : List (Operator Γ)) := (merged ops).map Prod.fst
def vectors {Γ : List Ty} (ops : List (Operator Γ)) := (merged ops).map Prod.snd

def carrierOp {k Γ}
    (r : UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)) : Operator Γ :=
  ⟨[Ty.curriedGround (k+1),Ty.curriedGround (k+1)],r.source,r.vector⟩

def callerOp {Γ} (src : OriginalTerm Γ (Ty.curriedGround 1))
    (v : OrdinalVector Γ 1) : Operator Γ :=
  ⟨[],src,v⟩

def scale (b : Nat) : Nat := 2^b

/-- One flat ordered list, preserving the multiplicity of every occurrence.
The caller source is the actual saturated caller, not a surrogate. -/
def paidList {Γ} (b : Nat) (xs : List (Operator Γ)) (caller : Operator Γ) : List (Operator Γ) :=
  (List.replicate (scale b) xs).flatten ++ List.replicate (scale b) caller

def gap (b count c : Nat) : Nat := scale b * (c-3*count-3)-1

noncomputable def chargedSum {Γ} (f : Nat → Nat) (xs : List (Operator Γ)) : Ordinal :=
  HeterogeneousUnaryAssembly.chargedSum (xs.map (fun x => CurrentReserve.unitValue f (x.vector 1)))

def operatorCode {Γ} (op : Operator Γ) : NumericUnaryChain.RawOperator :=
  (op.privateContext.map SyntaxCode.typeCode,SyntaxCode.encodeTerm op.term,OrdinalSyntax.vectorCode op.vector)

/-- Actual selected-policy assignment is made only after exact saturation. -/
def callerCode (p : Policy) (Γ : List Nat) (σ src : Nat) : Option NumericUnaryChain.RawOperator := do
  let τ ← SyntaxCode.check Γ src
  if τ=σ then
    let r ← TrackedSourceInspectionCode.arityCode σ
    if r=0 then none else
      let sat := NumericCarrierData.saturateSource (r-1) src
      let v ← PolicyAssignment.assignmentCode p Γ sat
      pure ([],sat,v)
  else none

/-- The final single lambda is a literal OriginalTerm source code. Its
chosen-policy complete vector is compiled, including the scalar. -/
def chainCode (p : Policy) (Γ : List Nat) (ops : List NumericUnaryChain.RawOperator) :
    Option (List Nat × Nat × List Nat) := do
  let ctx := NumericUnaryChain.contextCode Γ ops
  let src := NumericUnaryChain.chainCode ((NumericUnaryChain.mergeData ops).2.map Prod.fst)
  let v ← PolicyAssignment.assignmentCode p ctx src
  pure (ctx,src,v)

/-- The only scale is the original selected-policy body budget. The input
body/caller are not replaced; saturation belongs only to the flat chain.
All raw failure branches are deterministic and remain separate from the
well-typed generated-source correctness domain. -/
def compileCode (p : Policy) (Γ : List Nat) (σ body caller : Nat) :
    Option ((List Nat × Nat × List Nat) × Nat × Nat) := do
  if SyntaxCode.check (σ::Γ) body = some 0 then
    if TrackedSourceInspectionCode.occursCode 0 body then
      let (_,xs,c) ← CurrentGroundAccount.sourceCode p (σ::Γ) body
      let b ← CurrentGroundBudget.budgetCode p (σ::Γ) body
      let a ← callerCode p Γ σ caller
      let out ← chainCode p Γ (OriginalScaleCompilerCode.paidCode b xs a)
      pure (out,b,gap b xs.length c)
    else none
  else none

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction
