module
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedSupportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleAssignment
open AdmissibleSum

/-- Collect every actual coordinate, retaining the dependent finite index.
There is no default or out-of-range lookup. Any missing partial is failure. -/
def collect {α : Type} : (n : Nat) → (Fin n → Option α) → Option (Fin n → α)
  | 0, _ => some Fin.elim0
  | n + 1, f => do
      let a ← f 0
      let rest ← collect n (fun i => f i.succ)
      pure (Fin.cases a rest)

/-- Expand a repeat at its distinct source macro site. Count zero is a
specified totalization, never used for an actual scalar abstraction repeat. -/
def repeated {Γ : List Ty} (p : Policy) (site : MacroSite) (count : Nat)
    (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  match count with
  | 0 => .zero
  | k + 1 => expand (p.shape site k) (fun _ => t)

def numeral {Γ : List Ty} (p : Policy) (n : Nat) : OrdinalExpression Γ :=
  repeated p .numeral n .one

/-- The finite n contribution has an absent role exactly when n=0. No
value-based zero elimination or operand reassociation is performed. -/
def boxTail {Γ : List Ty} (p : Policy) (n : Nat)
    (f g : OrdinalExpression Γ) : OrdinalExpression Γ :=
  if n = 0 then .add f g
  else AdmissiblePartial.three p .optionalBoxTail f g (numeral p n)

def box {Γ : List Ty} {m n : Nat} (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) : OrdinalVector Γ m :=
  fun i => if i.val = 0 then
    .collapse (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1)
      (boxTail p n (f 0) (g 0))
  else ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i.val

def application {Γ : List Ty} {σ τ : Ty} (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level) :
    OrdinalVector Γ τ.level :=
  fun i => box p f g
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩

/-- Exact arbitrary-policy delta plus retained head closure. The high delta
coordinate is accessed only with a proof that it exists. No numeric zero
fallback substitutes for a missing actual coordinate. -/
def abstraction {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ :: Γ) m) :
    Option (OrdinalVector Γ (max (σ.level + 1) m)) := do
  let ps ← collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i))
  let factor := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
  pure fun j =>
    let delta : OrdinalExpression Γ :=
      if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
      else if hj : j.val < σ.level + 2 then
        expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
      else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
    if hm : j.val < m + 1 then .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩))
    else delta

/-- All actual original-T constructors, under the same fixed structural policy.
No policy's computability or original norm admissibility is assumed here. -/
def assignment {Γ : List Ty} {τ : Ty} (p : Policy) :
    OriginalTerm Γ τ → Option (OrdinalVector Γ τ.level)
  | .var v => some (fun i => .var ⟨_, v, i⟩)
  | .zeroC => some (fun _ => .one)
  | .succC => some (fun _ => .one)
  | .caseC _ => some (fun _ => .one)
  | .recC σ => some (fun i => if i.val = 0 then numeral p 2
      else if i.val = σ.level + 2 then .omega else .one)
  | .app f g => do
      let vf ← assignment p f
      let vg ← assignment p g
      pure (application p vf vg)
  | .lam body => do
      let vb ← assignment p body
      abstraction p vb
  | .ranked s _ => nomatch s

end LogicLineages.OrdinalComparison.Source.AdmissibleAssignment
