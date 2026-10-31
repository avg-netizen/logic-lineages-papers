module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecisionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler
open FirstOrder Language CotreePresburgerLinear CotreePresburgerUnit CotreePresburgerDecision

/-- Explicit variable map extension at a last-coordinate binder. -/
def extend {α : Type} {n k : Nat} (e : α ⊕ Fin n → Fin k) : α ⊕ Fin (n+1) → Fin (k+1) :=
  Sum.elim (fun a => (e (.inl a)).castSucc)
    (Fin.snoc (fun i => (e (.inr i)).castSucc) (Fin.last k))

/-- Equality is the conjunction of the two affine weak inequalities. -/
def equality {k : Nat} (s t : Affine k) : CotreePresburgerDecision.Formula k :=
  .conj (.atom (.nonneg (Affine.add s (Affine.scale (-1) t))))
    (.atom (.nonneg (Affine.add t (Affine.scale (-1) s))))

/-- Literal recursive compilation of pinned Mathlib first-order Presburger
syntax; there are no relation symbols in (0,1,+). -/
def compile {α : Type} : {n k : Nat} → presburger.BoundedFormula α n →
    (α ⊕ Fin n → Fin k) → CotreePresburgerDecision.Formula k
  | _, _, .falsum, _ => .bot
  | _, _, .equal s t, e => equality (Affine.ofTerm (s.relabel e)) (Affine.ofTerm (t.relabel e))
  | _, _, .rel r _, _ => Empty.elim r
  | _, _, .imp p q, e => .neg (.conj (compile p e) (.neg (compile q e)))
  | _, _, .all p, e => .neg (.ex (.neg (compile p (extend e))))

def ofFormula {n : Nat} (p : presburger.Formula (Fin n)) : CotreePresburgerDecision.Formula n :=
  compile p (Sum.elim id Fin.elim0)

/-- A total object-level decision value for the actual source formula syntax. -/
def evaluate {n : Nat} (p : presburger.Formula (Fin n)) (v : Fin n → Nat) : Bool :=
  CotreePresburgerDecision.evaluate (ofFormula p) (fun i => (v i : Int))

def satisfiable {n : Nat} (p : presburger.Formula (Fin n)) : Bool :=
  CotreePresburgerDecision.satisfiable (ofFormula p)
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler
