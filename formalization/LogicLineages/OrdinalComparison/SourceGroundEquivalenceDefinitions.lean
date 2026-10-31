module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionDefinitions
public import LogicLineages.OrdinalComparison.WWUnitObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundEquivalence
open OriginalDomain SourceCollisionCompletion

/-- A reference is intrinsically typed and can only address an earlier vertex. -/
abbrev Spec := List Ty × Ty
inductive Ref : List Spec → Spec → Type where
  | here {s ss} : Ref (s::ss) s
  | there {s t ss} : Ref ss s → Ref (t::ss) s
/-- Vertex contexts are local binder prefixes followed by the fixed shared
free context Γ. This makes lexical scope explicit in the source DAG. -/
abbrev Values (Γ : List Ty) (ss : List Spec) := ∀ {s}, Ref ss s → OriginalTerm (s.1++Γ) s.2

def extendValues {Γ ss s} (v : Values Γ ss) (t : OriginalTerm (s.1++Γ) s.2) : Values Γ (s::ss)
  | _, .here => t
  | _, .there r => v r
inductive DAG (Γ : List Ty) : List Spec → Type where
  | nil : DAG Γ []
  | var {ss Δ τ} : DAG Γ ss → Variable (Δ++Γ) τ → DAG Γ ((Δ,τ)::ss)
  | app {ss Δ σ τ} : DAG Γ ss → Ref ss (Δ,.arrow σ τ) → Ref ss (Δ,σ) → DAG Γ ((Δ,τ)::ss)
  | lam {ss Δ σ τ} : DAG Γ ss → Ref ss (σ::Δ,τ) → DAG Γ ((Δ,.arrow σ τ)::ss)
  | zero {ss Δ} : DAG Γ ss → DAG Γ ((Δ,.ground)::ss)
  | succ {ss Δ} : DAG Γ ss → DAG Γ ((Δ,.arrow .ground .ground)::ss)
  | case {ss Δ} : DAG Γ ss → (τ : Ty) → DAG Γ ((Δ,τ.caseType)::ss)
  | recursor {ss Δ} : DAG Γ ss → (τ : Ty) → DAG Γ ((Δ,τ.recType)::ss)

def DAG.values {Γ ss} : DAG Γ ss → Values Γ ss
  | .nil => fun r => nomatch r
  | .var d x => extendValues d.values (.var x)
  | .app (Δ:=Δ) (σ:=σ) (τ:=τ) d f a => extendValues (s:=(Δ,τ)) d.values (.app (σ:=σ) (τ:=τ) (d.values f) (d.values a))
  | .lam d b => extendValues d.values (.lam (d.values b))
  | .zero d => extendValues d.values .zeroC
  | .succ d => extendValues d.values .succC
  | .case d τ => extendValues d.values (.caseC τ)
  | .recursor d τ => extendValues d.values (.recC τ)

def Ref.map (f : Spec → Spec) {ss s} : Ref ss s → Ref (ss.map f) (f s)
  | .here => .here
  | .there r => .there (r.map f)
def insertSpec (s : Spec) : Spec := (s.1++[.ground],s.2)
def insertGround (Γ : List Ty) : (Δ : List Ty) → Renaming (Δ++Γ) ((Δ++[.ground])++Γ)
  | [] => Renaming.weaken Γ .ground
  | _::Δ => Renaming.lift (insertGround Γ Δ)
/-- One pass over the supplied primitive DAG: no vertex is duplicated. -/
def DAG.insert {Γ ss} : DAG Γ ss → DAG Γ (ss.map insertSpec)
  | .nil => .nil
  | .var (Δ:=Δ) d x => .var d.insert (insertGround Γ Δ x)
  | .app d f a => .app d.insert (f.map insertSpec) (a.map insertSpec)
  | .lam d b => .lam d.insert (b.map insertSpec)
  | .zero d => .zero d.insert
  | .succ d => .succ d.insert
  | .case d τ => .case d.insert τ
  | .recursor d τ => .recursor d.insert τ

structure Input (Γ : List Ty) (τ : Ty) where
  specs : List Spec
  graph : DAG Γ specs
  root : Ref specs ([],τ)
def Input.term {Γ τ} (d : Input Γ τ) : OriginalTerm Γ τ := d.graph.values d.root

/-- Typed source-context graft. The hole edge carries its capture-avoiding
renaming explicitly; it is a reference to the supplied DAG, not a copied
source tree. Context nodes themselves are literal original constructors. -/
inductive Context (Γ : List Ty) (τ : Ty) : List Ty → Ty → Type where
  | hole {Δ} : Renaming Γ Δ → Context Γ τ Δ τ
  | var {Δ σ} : Variable Δ σ → Context Γ τ Δ σ
  | zero {Δ} : Context Γ τ Δ .ground
  | app {Δ σ υ} : Context Γ τ Δ (.arrow σ υ) → Context Γ τ Δ σ → Context Γ τ Δ υ
  | lam {Δ σ υ} : Context Γ τ (σ::Δ) υ → Context Γ τ Δ (.arrow σ υ)

def Context.plug {Γ τ Δ υ} (t : OriginalTerm Γ τ) : Context Γ τ Δ υ → OriginalTerm Δ υ
  | .hole r => t.rename r
  | .var x => .var x
  | .zero => .zeroC
  | .app f a => .app (f.plug t) (a.plug t)
  | .lam b => .lam (b.plug t)
def Context.holes {Γ τ Δ υ} : Context Γ τ Δ υ → Nat
  | .hole _ => 1
  | .var _ | .zero => 0
  | .app f a => f.holes+a.holes
  | .lam b => b.holes
def Context.nodes {Γ τ Δ υ} : Context Γ τ Δ υ → Nat
  | .hole _ => 0
  | .var _ | .zero => 1
  | .app f a => f.nodes+a.nodes+1
  | .lam b => b.nodes+1

structure Graft (Γ : List Ty) where
  input : Input Γ .ground
  context : Context Γ .ground Γ .ground
def Graft.term {Γ} (d : Graft Γ) : OriginalTerm Γ .ground := d.context.plug d.input.term
def Graft.nodes {Γ} (d : Graft Γ) : Nat := d.input.specs.length+d.context.nodes

def magnify {Γ} (t : OriginalTerm Γ .ground) : OriginalTerm Γ .ground := eraser t .zeroC
def identity {Γ} : OriginalTerm Γ (.arrow .ground .ground) := .lam (.var .here)
def constant {Γ} : OriginalTerm Γ (.arrow .ground .ground) := .lam .zeroC
def lower {Γ} (t : OriginalTerm Γ .ground) : OriginalTerm Γ .ground := .app identity (magnify t)
def upper {Γ} (t : OriginalTerm Γ .ground) : OriginalTerm Γ .ground := .app constant (magnify t)

def magnifyContext (Γ : List Ty) : Context Γ .ground Γ .ground :=
  .app (.lam (.hole (Renaming.weaken Γ .ground))) .zero
def lowerContext (Γ : List Ty) : Context Γ .ground Γ .ground :=
  .app (.lam (.var .here)) (magnifyContext Γ)
def upperContext (Γ : List Ty) : Context Γ .ground Γ .ground :=
  .app (.lam .zero) (magnifyContext Γ)
def lowerGraft {Γ} (d : Input Γ .ground) : Graft Γ := ⟨d,lowerContext Γ⟩
def upperGraft {Γ} (d : Input Γ .ground) : Graft Γ := ⟨d,upperContext Γ⟩

/-- Literal primitive-DAG output, not a context-graft macro. -/
def magnifyInput {Γ} (d : Input Γ .ground) : Input Γ .ground :=
  let l := DAG.lam (Δ:=[]) d.graph.insert (d.root.map insertSpec)
  let z := DAG.zero (Δ:=[]) l
  let a := DAG.app z (.there .here) .here
  ⟨_,a,.here⟩
def identityInput {Γ} (d : Input Γ .ground) : Input Γ .ground :=
  let v := DAG.var (Δ:=[.ground]) d.graph (.here : Variable (.ground::Γ) .ground)
  let l := DAG.lam (Δ:=[]) v .here
  let a := DAG.app l .here (.there (.there d.root))
  ⟨_,a,.here⟩
def constantInput {Γ} (d : Input Γ .ground) : Input Γ .ground :=
  let v := DAG.zero (Δ:=[.ground]) d.graph
  let l := DAG.lam (Δ:=[]) v .here
  let a := DAG.app l .here (.there (.there d.root))
  ⟨_,a,.here⟩
def lowerInput {Γ} (d : Input Γ .ground) : Input Γ .ground := identityInput (magnifyInput d)
def upperInput {Γ} (d : Input Γ .ground) : Input Γ .ground := constantInput (magnifyInput d)

noncomputable def Weak {Γ} (a b : OriginalTerm Γ .ground) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat,
    rawScalar (valuation (UnitObservation.substitution ρ)) a ≤ rawScalar (valuation (UnitObservation.substitution ρ)) b
noncomputable def Strict {Γ} (a b : OriginalTerm Γ .ground) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat,
    rawScalar (valuation (UnitObservation.substitution ρ)) a < rawScalar (valuation (UnitObservation.substitution ρ)) b
end LogicLineages.OrdinalComparison.Source.GroundEquivalence
