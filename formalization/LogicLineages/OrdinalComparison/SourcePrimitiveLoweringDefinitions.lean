module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.PrimitiveLowering
open SourceAdditionCompletion SourceSortCompletion

abbrev Port := SourceAdditionCompletion.Atom

def Port.value {Γ} (ρ : OrdinalComponent Γ → Nat) : Port Γ → Nat
  | .zero => 0
  | .var x => input ρ x

inductive Gate (Γ : List Ty) where
  | eq (a b : Port Γ)
  | add (a b c : Port Γ)
  | sort (a b low high : Port Γ)
  | one (a : Port Γ)

def Gate.Holds {Γ} (ρ : OrdinalComponent Γ → Nat) : Gate Γ → Prop
  | .eq a b => a.value ρ = b.value ρ
  | .add a b c => a.value ρ + b.value ρ = c.value ρ
  | .sort a b l h => l.value ρ = min (a.value ρ) (b.value ρ) ∧ h.value ρ = max (a.value ρ) (b.value ρ)
  | .one a => a.value ρ = 1

/-- Only fixed-size local source expressions. Arbitrary supplied sources are
handled elsewhere by shared references, not embedded into this local grammar. -/
inductive Expr (Γ : List Ty) where
  | port (a : Port Γ)
  | successor (a : Port Γ)
  | erase (a b : Port Γ)
  | identityZero

def Expr.term {Γ} : Expr Γ → OriginalTerm Γ .ground
  | .port a => a.term
  | .successor a => .app .succC a.term
  | .erase a b => SourceAdditionCompletion.eraser a b
  | .identityZero => .app SourceAdditionCompletion.identity .zeroC

/-- Uniform fresh block. Old typed names retain their identity and order. -/
abbrev Block (Γ : List Ty) := List.replicate 9 Ty.ground ++ Γ

def shift (n : Nat) {Γ : List Ty} : Renaming Γ (List.replicate n Ty.ground ++ Γ) :=
  match n with
  | 0 => fun x => x
  | n+1 => fun x => .there (shift n x)

def fresh {Γ : List Ty} : {n : Nat} → Fin n → Variable (List.replicate n Ty.ground ++ Γ) .ground
  | n+1, i => Fin.cases .here (fun j => .there (fresh j)) i

def extend {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat) :
    (n : Nat) → (Fin n → Nat) → OrdinalComponent (List.replicate n Ty.ground ++ Γ) → Nat
  | 0, _, c => ρ c
  | n+1, z, ⟨_,.here,_⟩ => z 0
  | n+1, z, ⟨τ,.there x,j⟩ => extend ρ n (fun i => z i.succ) ⟨τ,x,j⟩

def liftPort {Γ} : Port Γ → Port (Block Γ)
  | .zero => .zero
  | .var x => .var (shift 9 x)

def aux {Γ} (i : Fin 9) : Port (Block Γ) := .var (fresh i)

def addEquations {Γ} (a b c d : Port Γ) : List (Expr Γ × Expr Γ) :=
  [(.erase b .zero,.erase .zero d),(.erase a d,.erase c .zero)]

def unused {Γ} (start : Nat) : List (Expr (Block Γ) × Expr (Block Γ)) :=
  ((List.finRange 9).filter (fun i => start ≤ i.val)).map (fun i => (.port (aux i),.port .zero))

/-- Each gate emits exactly ten actual source equations, sharing every old
port and all nine auxiliaries in one context. No independent input copies. -/
def lower {Γ} : Gate Γ → List (Expr (Block Γ) × Expr (Block Γ))
  | .eq a b => (.port (liftPort a),.port (liftPort b)) :: unused 0
  | .add a b c => addEquations (liftPort a) (liftPort b) (liftPort c) (aux 0) ++ unused 1
  | .sort a b l h =>
      [(.successor (liftPort a),.port (aux 0)),(.successor (liftPort b),.port (aux 1)),
       (.successor (liftPort l),.port (aux 2)),(.successor (liftPort h),.port (aux 3))] ++
      addEquations (aux 0) (aux 1) (aux 4) (aux 6) ++
      addEquations (aux 2) (aux 3) (aux 4) (aux 7) ++
      addEquations (liftPort l) (aux 5) (liftPort h) (aux 8)
  | .one a =>
      (.successor (aux 0),.identityZero) ::
      (addEquations (liftPort a) (liftPort a) (aux 0) (aux 1) ++ unused 2)

def SourceHolds {Γ} (ρ : OrdinalComponent Γ → Nat) (g : Gate Γ) (z : Fin 9 → Nat) : Prop :=
  ∀ e ∈ lower g, Equation (extend ρ 9 z) e.1.term e.2.term

/-- Numerical witnesses remain symbolic; no giant collapse value is run by
the source compiler, whose syntax above is entirely finite and executable. -/
noncomputable def canonicalWitness {Γ} (ρ : OrdinalComponent Γ → Nat) : Gate Γ → Fin 9 → Nat
  | .eq _ _ => ![0,0,0,0,0,0,0,0,0]
  | .add _ b _ => ![3*b.value ρ,0,0,0,0,0,0,0,0]
  | .sort a b l h =>
      let qa := successorObservation (a.value ρ); let qb := successorObservation (b.value ρ)
      let ql := successorObservation (l.value ρ); let qh := successorObservation (h.value ρ)
      let δ := max (a.value ρ) (b.value ρ) - min (a.value ρ) (b.value ρ)
      ![qa,qb,ql,qh,qa+qb,δ,3*qb,3*qh,3*δ]
  | .one a => ![2,3*a.value ρ,0,0,0,0,0,0,0]

/-- A primitive vertex for a port at any explicit local binder prefix. -/
def portDAG {Γ ss Δ} (d : GroundEquivalence.DAG Γ ss)
    (a : Port (Δ++Γ)) : GroundEquivalence.DAG Γ ((Δ,.ground)::ss) :=
  match a with
  | .zero => .zero d
  | .var x => .var d x

def Expr.graph {Γ} : Expr Γ → GroundEquivalence.Input Γ .ground
  | .port a => ⟨_,portDAG (Δ:=[]) .nil a,.here⟩
  | .successor a =>
      let v := portDAG (Δ:=[]) GroundEquivalence.DAG.nil a
      let s := GroundEquivalence.DAG.succ (Δ:=[]) v
      let t := GroundEquivalence.DAG.app s .here (.there .here)
      ⟨_,t,.here⟩
  | .erase a b =>
      let inner : Port (.ground::Γ) := match a with | .zero => .zero | .var x => .var (.there x)
      let v := portDAG (Δ:=[.ground]) GroundEquivalence.DAG.nil inner
      let l := GroundEquivalence.DAG.lam (Δ:=[]) v .here
      let arg := portDAG (Δ:=[]) l b
      let t := GroundEquivalence.DAG.app arg (.there .here) .here
      ⟨_,t,.here⟩
  | .identityZero =>
      let v := GroundEquivalence.DAG.var (Δ:=[.ground]) GroundEquivalence.DAG.nil (.here : Variable (.ground::Γ) .ground)
      let l := GroundEquivalence.DAG.lam (Δ:=[]) v .here
      let z := GroundEquivalence.DAG.zero (Δ:=[]) l
      let t := GroundEquivalence.DAG.app z (.there .here) .here
      ⟨_,t,.here⟩

def forest {Γ} (g : Gate Γ) : List (GroundEquivalence.Input (Block Γ) .ground × GroundEquivalence.Input (Block Γ) .ground) :=
  (lower g).map (fun e => (e.1.graph,e.2.graph))

def forestNodes {Γ} (g : Gate Γ) : Nat :=
  ((forest g).map (fun e => e.1.specs.length + e.2.specs.length)).sum
end LogicLineages.OrdinalComparison.Source.PrimitiveLowering
