module
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy

/-- The two admissible policies L and R from paper05 Appendix A. They differ
only in the ternary active-Add macro. All repeats and positive sums are left
combs, the exponential Repeat2 stays nested, and the box keeps its printed
right-associated optional tail. This is not a parametrization of all policies. -/
inductive ActiveSumAssociation where
  | left | right
  deriving DecidableEq

def sum3 {Γ : List Ty} (policy : ActiveSumAssociation)
    (a b c : OrdinalExpression Γ) : OrdinalExpression Γ :=
  match policy with
  | .left => .add (.add a b) c
  | .right => .add a (.add b c)

/-- A positive literalRepeat is a left comb with unchanged copies; the zero case is
only a totalization and does not silently delete any actual operand. -/
def literalRepeat {Γ : List Ty} (count : Nat) (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  match count with
  | 0 => .zero
  | k + 1 => (List.replicate k t).foldl (fun a b => .add a b) t

/-- Exact repaired policyPartial for the two policies, on the existing typed literal
ordinal grammar. Invalid active shapes return none. -/
def policyPartial {Γ : List Ty} {σ : Ty} (policy : ActiveSumAssociation) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) : Option (OrdinalPartialVector Γ σ) :=
  if ordinalHeadFree t then some (ordinalFreePartialVector i t) else
  match t with
  | .var ⟨_, _, k⟩ => if i = k.val then some (fun _ => .one) else none
  | .zero | .one | .omega => none
  | .add f g => do
      let pf ← policyPartial policy i f
      let pg ← policyPartial policy i g
      pure fun j => sum3 policy (pf j) (pg j) .one
  | .emul f g => if 0 < i then do
      let pf ← policyPartial policy (i + 1) f
      let pg ← policyPartial policy i g
      pure fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one
    else none
  | .collapse f g => if i = 0 then do
      let pf ← policyPartial policy 1 f
      let pg ← policyPartial policy 0 g
      pure fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j)
    else none

/-- Literal zero-history abstraction, including contextual missing-coordinate
elision. No actual zero subtree is removed. At a retained high coordinate the
head substitution records context erasure; equality to the unchanged tree is
an additional generated-support fact, not built into the syntax. -/
def abstraction {Γ : List Ty} {σ : Ty} {m : Nat} (policy : ActiveSumAssociation)
    (h : OrdinalVector (σ :: Γ) m) :
    Option (OrdinalVector Γ (max (σ.level + 1) m)) := do
  let ps ← (List.finRange (m + 1)).mapM (fun i => policyPartial policy i.val (h i))
  match ps with
  | [] => none
  | p0 :: rest =>
      let factor := 2 ^ (σ.level + 1) *
        ((List.finRange (m + 1)).map (fun i => ordinalPartialSize (h i))).sum
      pure fun j =>
        let delta : OrdinalExpression Γ :=
          if j.val = 0 then literalRepeat factor (p0 0)
          else if hj : j.val < σ.level + 2 then
            rest.foldl (fun a p => .add a (p ⟨j.val, hj⟩)) (p0 ⟨j.val, hj⟩)
          else if hm : j.val < m + 1 then ordinalHeadClosure (h ⟨j.val, hm⟩)
          else .zero
        if hm : j.val < m + 1 then .add delta (ordinalHeadClosure (h ⟨j.val, hm⟩))
        else delta

/-- Full syntax-directed original-T assignment under the chosen L/R policy.
This definition alone does not assert success, admissibility or bounded norm. -/
def assignment {Γ : List Ty} {τ : Ty} (policy : ActiveSumAssociation) :
    OriginalTerm Γ τ → Option (OrdinalVector Γ τ.level)
  | .var v => some (fun i => .var ⟨_, v, i⟩)
  | .zeroC => some (fun _ => .one)
  | .succC => some (fun _ => .one)
  | .caseC _ => some (fun _ => .one)
  | .recC σ => some (fun i => if i.val = 0 then .add .one .one
      else if i.val = σ.level + 2 then .omega else .one)
  | .app f g => do
      let vf ← assignment policy f
      let vg ← assignment policy g
      pure (ordinalCanonicalApplication vf vg)
  | .lam body => do
      let vb ← assignment policy body
      abstraction policy vb
  | .ranked s _ => nomatch s

/-- The actual typed, closed source lambda z:o. lambda x:o. ((lambda w:o. z) x).
No beta reduction is performed before assignment. -/
def witness : OriginalTerm [] (.arrow .ground (.arrow .ground .ground)) :=
  .lam (.lam (.app (.lam (.var (.there (.there .here)))) (.var .here)))

/-- Refusing evaluator for positive finite closed Add trees. It never assigns a
surrogate value to a variable, omega, ExpProd or collapse. The witness's
positive output needs only One and Add. Soundness against `denote` is separate. -/
def finiteAddValue {ι : Type} :
    LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Option Nat
  | .one => some 1
  | .add f g => do
      let a ← finiteAddValue f
      let b ← finiteAddValue g
      pure (a + b)
  | _ => none

def witnessPositive (policy : ActiveSumAssociation) : Option (OrdinalExpression []) := do
  let v ← assignment policy witness
  pure (v 1)

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
