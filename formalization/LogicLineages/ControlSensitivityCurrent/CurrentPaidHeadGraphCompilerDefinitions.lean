module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphLayoutDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open CurrentUnitElimination (WireCtx shift groundWireCtx allGroundReplicate pinGround)
open RawSourceDAG.InputCompiler (InputCode)
open RawSourceDAG.PlanComparison (OutputCode)

noncomputable def exactPoints (f : Nat → Nat) (ξ : Ordinal) (base : Nat) : List Nat :=
  let n := actualOrdinalNorm ξ
  (List.range (max n base-n)).map (fun i => J f ξ (n+i))

def smallValues (f : Nat → Nat) : List Nat := (List.range 4).map f

noncomputable def typedDirect {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground)
    (f : Nat → Nat) (β : Ordinal) (c δ : Nat)
    (r : CurrentUnitElimination.OpenGraph (.ground :: Γ)) : Presented DirectCtx :=
  let ξ := shiftHead β δ
  let base := RayBase β c
  direct hg δ (actualOrdinalNorm ξ) base (smallValues f) (exactPoints f ξ base) r

/-- Typed arithmetic code for the actual same q.matrix, not a quotient by
satisfiability. Prefix width is part of the raw result. -/
def presentedCode {Γ : List Ty} (q : Presented Γ) : UnitCode.Block :=
  (q.width,MatrixCode.formula q.matrix)

noncomputable def pointValuesCode (f : Nat → Nat) (ξ base : Nat) : List Nat :=
  let n := rawNormCode ξ
  (List.range (max n base-n)).map (fun i => valueCode f ξ (n+i))

def directBlock (g : Nat) (ray : UnitCode.Block) (δ nξ base : Nat)
    (small points : List Nat) : UnitCode.Block :=
  let w := directWidth ray.1 δ
  let table := (List.range (ray.1+2+g)).map (rayPlacement ray.1)
  let r := MatrixCode.renameFormula (UnitCode.bitCtx (w+2)) table ray.2
  (w,directBody rawLayout ray.1 δ nξ base small points r)

def insertedBlock (g nξ level : Nat) (b c d : UnitCode.Block) : UnitCode.Block :=
  let w := insertedWidth b.1 c.1 d.1
  let ctx := UnitCode.bitCtx (w+1+g)
  let l := MatrixCode.renameFormula ctx
    ((List.range (b.1+1+g)).map (placeB b.1 c.1 d.1)) b.2
  let r := MatrixCode.renameFormula ctx
    ((List.range (c.1+1+g)).map (placeC b.1 c.1 d.1)) c.2
  let q := MatrixCode.renameFormula ctx
    ((List.range (d.1+2)).map (placeGraph b.1 c.1 d.1)) d.2
  (w,insertedBody rawLayout b.1 c.1 d.1 nξ level l r q)

abbrev KInput := List Nat × Nat × Nat
abbrev OriginalInput := List Nat × Nat × Nat × KInput

/-- Exact supplied arbitrary K and finite Δ; certificate validity controls
source correctness, not termination of this total all-raw program. -/
noncomputable def directPacket (p : Policy) (f : Nat → Nat) (k : KInput) :
    Option (UnitCode.Block × Nat) := do
  let (Γ,src,δ) := k
  let (β,ξ,c) ← parameterCode p f Γ src δ
  let (Ξ,a) ← auxiliaryCode Γ src
  let ray ← UnitCode.block p f Ξ a
  let base := rawNormCode β+c+1
  let n := rawNormCode ξ
  pure (directBlock (groundCount (Ξ.tail)) ray δ n base (smallValues f) (pointValuesCode f ξ base),n)

noncomputable def directCode (p : Policy) (f : Nat → Nat) (k : KInput) : Option UnitCode.Block :=
  (directPacket p f k).map Prod.fst

/-- B and C are the exact input codes in their same original Γ, unchanged.
Separate observation compilers share their entire old ground suffix. -/
noncomputable def insertCode (p : Policy) (f : Nat → Nat) (data : OriginalInput) : Option UnitCode.Block := do
  let (Γ,B,C,k) := data
  let σ ← SyntaxCode.check Γ C
  let b ← UnitCode.block p f Γ B
  let c ← UnitCode.block p f Γ C
  let (d,n) ← directPacket p f k
  pure (insertedBlock (groundCount Γ) n (SyntaxCode.typeLevel σ) b c d)

/-- One fiber only temporarily pins the actual original external values at
the very end. Its satisfaction is not used in place of an open-graph theorem. -/
def closeAt {Γ : List Ty} (a : Presented Γ) (hg : ∀ σ ∈ Γ, σ = .ground)
    (ρ : Variable Γ .ground → Nat) : SourceAST.Sentence :=
  let Ξ := WireCtx a.width Γ
  let e : Ξ = List.replicate Ξ.length .ground :=
    allGroundReplicate Ξ (groundWireCtx a.width Γ hg)
  let pins := pinGround Γ (shift a.width) ρ
  ⟨Ξ.length,e ▸ SourceAST.Formula.conj a.matrix pins⟩

def externalValues : {Γ : List Ty} → (Variable Γ .ground → Nat) → List Nat
  | [],_ => []
  | .ground :: _,ρ => ρ .here :: externalValues (fun x => ρ (.there x))
  | .arrow _ _ :: _,ρ => externalValues (fun x => ρ (.there x))

def pinCode : Nat → List Nat → Nat
  | _,[] => 0
  | i,v::vs => MatrixCode.both (MatrixCode.eq (MatrixCode.var i) (MatrixCode.lit v)) (pinCode (i+1) vs)

def fiberInputCode (d : UnitCode.Block) (values : List Nat) : Nat × InputCode :=
  (d.1+values.length,MatrixCode.inputCode (MatrixCode.both d.2 (pinCode d.1 values)))

def compiledFiberCode (d : UnitCode.Block) (values : List Nat) : OutputCode :=
  CurrentCompiler.compile (fiberInputCode d values)

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
