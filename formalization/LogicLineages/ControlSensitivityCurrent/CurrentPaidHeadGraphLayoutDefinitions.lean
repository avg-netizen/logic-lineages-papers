module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphUnitCodeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence
open CurrentUnitElimination (WireCtx shift)

/-- One literal finite graph layout instantiated both by the actual typed
SourceAST and its arithmetic syntax code. All witnesses are explicit names. -/
structure Layout (Term Form : Type) where
  var : Nat → Term
  lit : Nat → Term
  add : Term → Term → Term
  succCall : Term → Term
  eq : Term → Term → Form
  le : Term → Term → Form
  and : Form → Form → Form
  or : Form → Form → Form
  yes : Form
  no : Form

def actualS : Input [] (.arrow .ground .ground) :=
  CurrentTreeInputCoverage.input (.succC : OriginalTerm [] (.arrow .ground .ground))

def rawLayout : Layout Nat Nat where
  var := MatrixCode.var
  lit := MatrixCode.lit
  add := MatrixCode.add
  succCall := MatrixCode.unary (RawSourceDAG.encode ⟨[],.arrow .ground .ground,actualS⟩)
  eq := MatrixCode.eq
  le := MatrixCode.le
  and := MatrixCode.both
  or := MatrixCode.either
  yes := 0
  no := 1

def slot {Γ : List Ty} (fallback : Variable Γ .ground) (i : Nat) : Variable Γ .ground :=
  (RawSourceDAG.getVariable Γ .ground i).getD fallback

def typedLayout {Γ : List Ty} (fallback : Variable Γ .ground) :
    Layout (SourceAST.Term Γ) (SourceAST.Formula Γ) where
  var := fun i => .var (slot fallback i)
  lit := .literal
  add := .add
  succCall := .unary actualS
  eq := .eq
  le := .le
  and := .conj
  or := .disj
  yes := .truth
  no := .falsity

def fGate {A F} (l : Layout A F) (small : List Nat) (u v arg : Nat) : F :=
  ((List.range 4).map (fun j => l.and (l.eq (l.var u) (l.lit j))
      (l.eq (l.var v) (l.lit (small.getD j 0))))).foldr l.or
    (l.and (l.eq (l.var u) (l.add (l.var arg) (l.lit 4)))
      (l.eq (l.var v) (l.succCall (l.var arg))))

/-- Witness order: ray locals, encoded ray output, z's natural variable,
zero for auxiliary ground captures, u₀…uΔ, then Δ S-gate arguments. -/
def directWidth (ray Δ : Nat) := ray+3+(Δ+1)+Δ
def uSlot (ray j : Nat) := ray+3+j
def argSlot (ray Δ j : Nat) := ray+3+(Δ+1)+j

def rayPlacement (ray i : Nat) := if i≤ray+1 then i else ray+2

def tailBody {A F} (l : Layout A F) (wr δ nξ base : Nat) (small : List Nat) (ray : F) : F :=
  let t := directWidth wr δ
  let u := uSlot wr
  let rels := [l.le (l.lit (max nξ base)) (l.var t), l.eq (l.var (u 0)) (l.var t),
    l.eq (l.var (wr+2)) (l.lit 0),
    l.eq (l.var (u δ)) (l.add (l.lit base) (l.var (wr+1))),ray,
    l.eq (l.var (t+1)) (l.add (l.var wr) (l.lit (δ+1)))]
  let gates := (List.range δ).map (fun j => fGate l small (u j) (u (j+1)) (argSlot wr δ j))
  (rels++gates).foldr l.and l.yes

/-- Literal ordered enumeration, one exact value for each genuine finite
input starting at Nξ, and no global ray/range constraint. -/
def prefixBody {A F} (l : Layout A F) (t y : Nat) : Nat → List Nat → F
  | _,[] => l.no
  | first,v::vs => l.or (l.and (l.eq (l.var t) (l.lit first)) (l.eq (l.var y) (l.lit v)))
      (prefixBody l t y (first+1) vs)

def directBody {A F} (l : Layout A F) (wr δ nξ base : Nat)
    (small points : List Nat) (ray : F) : F :=
  let t := directWidth wr δ
  l.or (prefixBody l t (t+1) nξ points) (tailBody l wr δ nξ base small ray)

/-- Original B/C fixed source blocks have a common ground suffix, never
independent copies. The compiler allocates only the numerical splice t. -/
def operandEnd (b c g : Nat) := b+c+g
def insertedWidth (b c g : Nat) := operandEnd b c g+3

def placeB (b c g i : Nat) : Nat :=
  if i<b then i else if i=b then operandEnd b c g else insertedWidth b c g+(i-b)
def placeC (b c g i : Nat) : Nat :=
  if i<c then b+i else if i=c then operandEnd b c g+1 else insertedWidth b c g+(i-c)
def placeGraph (b c g i : Nat) : Nat := if i<g then b+c+i else b+c+i+2

def insertedBody {A F} (l : Layout A F) (wb wc wg nξ level : Nat) (b c graph : F) : F :=
  let i := operandEnd wb wc wg
  l.and (l.and b c)
    (l.and (l.eq (l.var (i+2)) (l.add (l.add (l.lit (nξ+level+2)) (l.var i)) (l.var (i+1)))) graph)

/-- Genuine open fiber under an explicit finite existential prefix. -/
structure Presented (Γ : List Ty) where
  width : Nat
  matrix : SourceAST.Formula (WireCtx width Γ)

noncomputable def Presented.holds {Γ : List Ty} (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (a : Presented Γ) (ρ : Variable Γ .ground → Nat) : Prop :=
  ∃ μ : Variable (WireCtx a.width Γ) .ground → Nat,
    (∀ x, μ (shift a.width x) = ρ x) ∧ a.matrix.eval p f μ = true

def varMem {Γ : List Ty} {σ : Ty} (x : Variable Γ σ) : σ ∈ Γ := by
  induction x with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

/-- The numeric table, typed using actual ground contexts. Only invalid
numeric positions would select the final fallback. -/
def route {Γ Ξ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground)
    (fallback : Variable Ξ .ground) (index : Nat → Nat) : Renaming Γ Ξ := fun {σ} x =>
  let h := hg σ (varMem x)
  cast (congrArg (Variable Ξ) h.symm) (slot fallback (index (RawSourceDAG.variableIndex x)))

abbrev DirectCtx : List Ty := [.ground,.ground]

def endValues (t y : Nat) : Variable DirectCtx .ground → Nat
  | .here => t
  | .there .here => y
  | .there (.there x) => nomatch x

def resultValues {Γ : List Ty} (ρ : Variable Γ .ground → Nat) (y : Nat) :
    Variable (.ground :: Γ) .ground → Nat
  | .here => y
  | .there x => ρ x

open CurrentUnitElimination (OpenGraph groundWireCtx renameFormula)

def direct {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground)
    (δ nξ base : Nat) (small points : List Nat) (r : OpenGraph (.ground :: Γ)) : Presented DirectCtx :=
  let w := directWidth r.width δ
  let z : Variable (WireCtx w DirectCtx) .ground := shift w .here
  let allGround := groundWireCtx r.width (.ground :: .ground :: Γ)
    (fun σ h => by
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      exact hg σ h)
  let ray := renameFormula (route allGround z (rayPlacement r.width)) r.matrix
  ⟨w,directBody (typedLayout z) r.width δ nξ base small points ray⟩

def inserted {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat)
    (B C : OpenGraph Γ) (g : Presented DirectCtx) : Presented (.ground :: Γ) :=
  let w := insertedWidth B.width C.width g.width
  let z : Variable (WireCtx w (.ground :: Γ)) .ground := shift w .here
  let allB := groundWireCtx B.width (.ground :: Γ)
    (fun σ h => by rcases List.mem_cons.mp h with rfl|h; rfl; exact hg σ h)
  let allC := groundWireCtx C.width (.ground :: Γ)
    (fun σ h => by rcases List.mem_cons.mp h with rfl|h; rfl; exact hg σ h)
  let allG := groundWireCtx g.width DirectCtx (fun σ h => by simpa [DirectCtx] using h)
  let b := renameFormula (route allB z (placeB B.width C.width g.width)) B.matrix
  let c := renameFormula (route allC z (placeC B.width C.width g.width)) C.matrix
  let graph := renameFormula (route allG z (placeGraph B.width C.width g.width)) g.matrix
  ⟨w,insertedBody (typedLayout z) B.width C.width g.width nξ level b c graph⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
