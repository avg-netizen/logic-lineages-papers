module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScopedDAG
open GroundEquivalence

def Ref.front (tail : List Spec) {ss s} : Ref ss s → Ref (ss++tail) s
  | .here => .here
  | .there r => .there (Ref.front tail r)
def Ref.back (front : List Spec) {ss s} (r : Ref ss s) : Ref (front++ss) s :=
  match front with
  | [] => r
  | _::front => .there (Ref.back front r)

/-- Append literal vertices; every old reference remains a single reference. -/
def append {Γ ss tt} (a : DAG Γ ss) : DAG Γ tt → DAG Γ (tt++ss)
  | .nil => a
  | .var d x => .var (append a d) x
  | .app d f x => .app (append a d) (Ref.front ss f) (Ref.front ss x)
  | .lam d b => .lam (append a d) (Ref.front ss b)
  | .zero d => .zero (append a d)
  | .succ d => .succ (append a d)
  | .case d τ => .case (append a d) τ
  | .recursor d τ => .recursor (append a d) τ

def prefixRename {Γ Δ} (r : Renaming Γ Δ) : (ps : List Ty) → Renaming (ps++Γ) (ps++Δ)
  | [] => r
  | _::ps => Renaming.lift (prefixRename r ps)
def rename {Γ Δ ss} (r : Renaming Γ Δ) : DAG Γ ss → DAG Δ ss
  | .nil => .nil
  | .var (Δ:=ps) d x => .var (rename r d) (prefixRename r ps x)
  | .app d f a => .app (rename r d) f a
  | .lam d b => .lam (rename r d) b
  | .zero d => .zero (rename r d)
  | .succ d => .succ (rename r d)
  | .case d τ => .case (rename r d) τ
  | .recursor d τ => .recursor (rename r d) τ

def renameInput {Γ Δ τ} (r : Renaming Γ Δ) (d : Input Γ τ) : Input Δ τ :=
  ⟨d.specs,rename r d.graph,d.root⟩
def zero (Γ : List Ty) : Input Γ .ground := ⟨_,DAG.zero (Δ:=[]) .nil,.here⟩
def variableInput {Γ τ} (x : Variable Γ τ) : Input Γ τ := ⟨_,DAG.var (Δ:=[]) .nil x,.here⟩
def successor (Γ : List Ty) : Input Γ (.arrow .ground .ground) := ⟨_,DAG.succ (Δ:=[]) .nil,.here⟩
def application {Γ σ τ} (f : Input Γ (.arrow σ τ)) (a : Input Γ σ) : Input Γ τ :=
  let d := append f.graph a.graph
  let p := Ref.back a.specs f.root
  let q := Ref.front f.specs a.root
  ⟨_,DAG.app d p q,.here⟩
def eraser {Γ} (a b : Input Γ .ground) : Input Γ .ground :=
  let d := append a.graph.insert b.graph
  let p := Ref.back b.specs (a.root.map insertSpec)
  let q := Ref.front (a.specs.map insertSpec) b.root
  let l := DAG.lam (Δ:=[]) d p
  ⟨_,DAG.app l .here (.there q),.here⟩
def detectorLeft {Γ} (a b : Input Γ .ground) : Input Γ .ground :=
  eraser (eraser a a) (eraser b b)
def detectorRight {Γ} (a b : Input Γ .ground) : Input Γ .ground :=
  eraser (eraser a b) (eraser b a)
def aggregate {Γ} : List (Input Γ .ground × Input Γ .ground) → Input Γ .ground × Input Γ .ground
  | [] => (zero Γ,zero Γ)
  | (p,q)::es =>
    let tail := aggregate es
    (eraser (detectorLeft p q) tail.1,eraser (detectorRight p q) tail.2)
def equations {Γ} (es : List (Input Γ .ground × Input Γ .ground)) :=
  es.map (fun e => (e.1.term,e.2.term))
def weight {Γ} (es : List (Input Γ .ground × Input Γ .ground)) : Nat :=
  (es.map (fun e => 2*(e.1.specs.length+e.2.specs.length)+8)).sum+1
end LogicLineages.OrdinalComparison.Source.ScopedDAG
