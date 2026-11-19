module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentAbsoluteDefinitions
public import LogicLineages.ControlSensitivityCurrent.SourceASTFormulaDefinitions
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence CurrentOneUnit

/-- Delete just the functional free slots, preserving the ground slots in
their original order. Neither repeated syntax occurrences nor evaluation
values are used to decide which slots survive. -/
def groundCtx : List Ty → List Ty
  | [] => []
  | .ground :: Γ => .ground :: groundCtx Γ
  | .arrow _ _ :: Γ => groundCtx Γ

def oldGround : {Γ : List Ty} → Variable (groundCtx Γ) .ground → Variable Γ .ground
  | [], x => nomatch x
  | .ground :: _, .here => .here
  | .ground :: _, .there x => .there (oldGround x)
  | .arrow _ _ :: _, x => .there (oldGround x)

def groundOnlyContext (Γ : List Ty) : ∀ σ ∈ groundCtx Γ, σ = .ground := by
  induction Γ with
  | nil => simp [groundCtx]
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      intro t ht
      change t ∈ .ground :: groundCtx Γ at ht
      rcases List.mem_cons.mp ht with h | h
      · exact h
      · exact ih t h
    | arrow a b => exact ih

theorem groundCtx_of_ground (Γ : List Ty) (hg : ∀ σ ∈ Γ, σ = .ground) :
    groundCtx Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hσ := hg σ (by simp)
    obtain rfl := hσ
    exact congrArg (List.cons Ty.ground) (ih (fun t ht => hg t (by simp [ht])))

theorem groundCtx_remove (left right : List Ty) (σ : Ty) (hσ : 0 < σ.level) :
    groundCtx (left ++ σ :: right) = groundCtx (left ++ right) := by
  induction left with
  | nil =>
    cases σ with
    | ground => simp [Ty.level] at hσ
    | arrow a b => rfl
  | cons a left ih =>
    cases a with
    | ground => exact congrArg (List.cons Ty.ground) ih
    | arrow a b => exact ih

/-- Literal proof-free payload: the constructors store the source, selected
slot and linear row, not an assumption about that row's semantics. -/
inductive Tree : List Ty → Type where
  | leaf {Γ τ} (allGround : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) : Tree Γ
  | free (left right : List Ty) (σ : Ty) (functional : 0 < σ.level)
      (row : LinearCode) (q : Tree (left ++ right)) : Tree (left ++ σ :: right)
  | active (left right : List Ty) (σ : Ty) (functional : 0 < σ.level)
      (row : LinearCode) (q r : Tree (left ++ right)) : Tree (left ++ σ :: right)

def step (p : AdmissibleSum.Policy)
    (rec : {Γ : List Ty} → {τ : Ty} → OriginalTerm Γ τ → Option (Tree Γ)) :
    {Γ : List Ty} → {τ : Ty} → UnitElimination.Selection Γ → OriginalTerm Γ τ → Option (Tree Γ)
  | _,_,.ground hg,a => some (.leaf hg (CurrentTreeInputCoverage.input a))
  | _,τ,.found left right σ hs,a => do
    let b := a.rename (SelectedBinder.moveToHead left right σ)
    let d ← typedCoefficients p b
    let q ← rec (OneUnit.first b)
    let row := equation τ.level d
    if d.2.2 then
      return .free left right σ hs row q
    else
      let r ← rec (OneUnit.second b)
      return .active left right σ hs row q r

/-- Recursion is structural in fuel. Every call occurs only after removing
the same actual chosen functional slot; the added unused u is bound, not in
the remaining input list. -/
def build (p : AdmissibleSum.Policy) :
    (fuel : Nat) → {Γ : List Ty} → {τ : Ty} → OriginalTerm Γ τ → Option (Tree Γ)
  | 0,_,_,_ => none
  | n+1,Γ,_,a => step p (fun {_ _} b => build p n b) (UnitElimination.select Γ) a

def depth {Γ} : Tree Γ → Nat
  | .leaf _ _ => 0
  | .free _ _ _ _ _ q => depth q + 1
  | .active _ _ _ _ _ q r => max (depth q) (depth r) + 1

/-- Explicit raw positive output convention: each internal AST scalar wire
of value n represents actual raw n+1, while ground original wires are the
existing encoded coordinate literals. -/
def WireCtx : Nat → List Ty → List Ty
  | 0,Γ => Γ
  | n+1,Γ => .ground :: WireCtx n Γ

def shift (n : Nat) {Γ : List Ty} : Renaming Γ (WireCtx n Γ) :=
  match n with
  | 0 => fun x => x
  | n+1 => fun x => .there (shift n x)

def under {Γ Δ : List Ty} (r : Renaming Γ Δ) :
    (n : Nat) → Renaming (WireCtx n Γ) (WireCtx n Δ)
  | 0 => r
  | n+1 => Renaming.lift (under r n)

/-- Choose exactly one new position for the former result wire; preserve the
actual old witness/ground embedding for every other slot. -/
def reroute {Γ Δ : List Ty} :
    (n : Nat) → Renaming (WireCtx n Γ) Δ → Variable Δ .ground →
      Renaming (WireCtx n (.ground :: Γ)) Δ
  | 0,_,z,_,.here => z
  | 0,r,_,_,.there x => r x
  | n+1,r,_,_,.here => r .here
  | n+1,r,z,_,.there x => reroute n (fun x => r (.there x)) z x

theorem wireCtx_add (m n : Nat) (Γ : List Ty) :
    WireCtx (m+n) Γ = WireCtx m (WireCtx n Γ) := by
  induction m with
  | zero => simp only [Nat.zero_add,WireCtx]
  | succ m ih => simp only [Nat.succ_add,WireCtx,ih]

def renameTerm {Γ Δ : List Ty} (r : Renaming Γ Δ) :
    SourceAST.Term Γ → SourceAST.Term Δ
  | .var x => .var (r x)
  | .literal n => .literal n
  | .add a b => .add (renameTerm r a) (renameTerm r b)
  | .unary a b => .unary a (renameTerm r b)
  | .observation a => .observation (ScopedDAG.renameInput r a)

def renameFormula {Γ Δ : List Ty} (r : Renaming Γ Δ) :
    SourceAST.Formula Γ → SourceAST.Formula Δ
  | .truth => .truth
  | .falsity => .falsity
  | .eq a b => .eq (renameTerm r a) (renameTerm r b)
  | .le a b => .le (renameTerm r a) (renameTerm r b)
  | .lt a b => .lt (renameTerm r a) (renameTerm r b)
  | .neg a => .neg (renameFormula r a)
  | .conj a b => .conj (renameFormula r a) (renameFormula r b)
  | .disj a b => .disj (renameFormula r a) (renameFormula r b)

def times {Γ : List Ty} : Nat → SourceAST.Term Γ → SourceAST.Term Γ
  | 0,_ => .literal 0
  | n+1,a => .add a (times n a)

def raw {Γ : List Ty} (x : Variable Γ .ground) : SourceAST.Term Γ :=
  .add (.var x) (.literal 1)

def rowFormula {Γ : List Ty} (row : LinearCode) (l l' r : SourceAST.Term Γ) :
    SourceAST.Formula Γ :=
  .eq (.add (times row.1 l) (.literal row.2.1))
    (.add (.add (times row.2.2.1 l') (times row.2.2.2.1 r)) (.literal row.2.2.2.2))

/-- A genuine existential natural prefix and a literal current E_src AST.
The outer free interface consists of the result wire followed by the
original shared ground wires. -/
structure OpenGraph (Γ : List Ty) where
  width : Nat
  matrix : SourceAST.Formula (WireCtx width (.ground :: Γ))

noncomputable def OpenGraph.holds {Γ : List Ty} (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (q : OpenGraph Γ) (ρ : Variable Γ .ground → Nat) (v : Nat) : Prop :=
  ∃ ω : Variable (WireCtx q.width (.ground :: Γ)) .ground → Nat,
    (∀ x, ω (shift q.width (.there x)) = ρ x) ∧
    ω (shift q.width .here) = v ∧ q.matrix.eval p f ω = true

/-- A leaf keeps two actual eraser applications, form factor, and literal
current closed-source anchor. The leaf's input result type is unrestricted. -/
noncomputable def groundGraph (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {τ : Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (a : Input Γ τ) : OpenGraph Γ :=
  let lift : Renaming (.ground :: .ground :: Γ) (.ground :: .ground :: .ground :: Γ) :=
    Renaming.lift (Renaming.lift (Renaming.weaken Γ .ground))
  let l := ScopedDAG.renameInput lift (AbsoluteProbeDAG.originalInput a)
  let r := ScopedDAG.renameInput lift (AbsoluteProbeDAG.closedInput hg a)
  let C := CurrentAbsolute.anchor p f (RawSourceDAG.encode ⟨Γ,τ,a⟩)
  let d := AbsoluteObserver.factor τ
  ⟨2,.conj (.eq (.observation l) (.observation r))
    (.eq (.add (times d (raw (.there (.there .here)))) (raw .here))
      (.add (.literal (d*C)) (raw (.there .here))))⟩

def freeGraph {Γ : List Ty} (row : LinearCode) (q : OpenGraph Γ) : OpenGraph Γ :=
  let Γ' := .ground :: WireCtx q.width (.ground :: Γ)
  let r₀ : Renaming (WireCtx q.width Γ) Γ' :=
    fun x => .there (under (Renaming.weaken Γ .ground) q.width x)
  let r : Renaming (WireCtx q.width (.ground :: Γ)) Γ' := reroute q.width r₀ .here
  ⟨q.width+1,.conj (renameFormula r q.matrix)
    (rowFormula row (raw (.here : Variable Γ' .ground)) (.literal 0)
      (raw (.there (shift q.width .here))))⟩

def activeGraph {Γ : List Ty} (row : LinearCode) (q s : OpenGraph Γ) : OpenGraph Γ :=
  let base := .ground :: Γ
  let Γ' := .ground :: .ground :: WireCtx q.width (WireCtx s.width base)
  let l₀ : Renaming (WireCtx q.width Γ) Γ' :=
    fun x => .there (.there (under (fun x => shift s.width (.there x))
      q.width x))
  let r₀ : Renaming (WireCtx s.width Γ) Γ' :=
    fun x => .there (.there (shift q.width (under (Renaming.weaken Γ .ground) s.width x)))
  let left := renameFormula (reroute q.width l₀ .here) q.matrix
  let right := renameFormula (reroute s.width r₀ (.there .here)) s.matrix
  let result := raw (.there (.there (shift q.width (shift s.width .here))) : Variable Γ' .ground)
  let m := SourceAST.Formula.conj (.conj left right)
    (rowFormula row (raw (.here : Variable Γ' .ground)) (raw (.there .here)) result)
  ⟨(q.width+s.width)+2,
    renameFormula (fun {τ} x => cast (congrArg (fun Δ => Variable (.ground :: .ground :: Δ) τ)
      (wireCtx_add q.width s.width base).symm) x) m⟩

noncomputable def render (p : AdmissibleSum.Policy) (f : Nat → Nat) :
    {Γ : List Ty} → Tree Γ → OpenGraph (groundCtx Γ)
  | Γ,.leaf hg a => (groundCtx_of_ground Γ hg).symm ▸ groundGraph p f hg a
  | _,.free left right σ hs row q =>
    (groundCtx_remove left right σ hs).symm ▸ freeGraph row (render p f q)
  | _,.active left right σ hs row q r =>
    (groundCtx_remove left right σ hs).symm ▸ activeGraph row (render p f q) (render p f r)

end LogicLineages.ControlSensitivityCurrent.CurrentUnitElimination
