module
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
public import LogicLineages.OrdinalComparison.SourceSortCompletionDefinitions
public import LogicLineages.OrdinalComparison.SourceTypedPortsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic

/-- Finite source-arithmetic terms. Multiplication is only by a fixed numeral. -/
inductive Expr where
  | numeral : Nat → Expr
  | variable : Nat → Expr
  | add : Expr → Expr → Expr
  | scale : Nat → Expr → Expr

def Expr.value (ν : Nat → Nat) : Expr → Nat
  | .numeral n => n
  | .variable i => ν i
  | .add a b => a.value ν + b.value ν
  | .scale n a => n * a.value ν

def Expr.rename (r : Nat → Nat) : Expr → Expr
  | .numeral n => .numeral n
  | .variable i => .variable (r i)
  | .add a b => .add (a.rename r) (b.rename r)
  | .scale n a => .scale n (a.rename r)

def Expr.lift (k : Nat) (a : Expr) : Expr := a.rename (fun i => i+k)

def extend (ν : Nat → Nat) (n : Nat) : Nat → Nat
  | 0 => n
  | i+1 => ν i

/-- Literal finite existential source arithmetic. A source atom contains an
actual ground-output source, a proof that its context is all ground, and a
finite tuple of argument expressions. No graph predicate, ordinal evaluator,
functional observation, or iteration primitive is a constructor. -/
inductive Formula where
  | truth
  | falsity
  | eq : Expr → Expr → Formula
  | le : Expr → Expr → Formula
  | observation {Γ : List Ty} : (∀ σ ∈ Γ, σ=Ty.ground) →
      OriginalTerm Γ .ground → List Expr → Expr → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | existsNat : Formula → Formula

noncomputable def Formula.eval (ν : Nat → Nat) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .eq a b => a.value ν = b.value ν
  | .le a b => a.value ν ≤ b.value ν
  | .observation _ t xs y => AbsoluteObserver.Observation
      (fun c => (xs.getD (SourceTypedPorts.variableIndex c.2.1) (.numeral 0)).value ν)
      t (y.value ν)
  | .and p q => p.eval ν ∧ q.eval ν
  | .or p q => p.eval ν ∨ q.eval ν
  | .existsNat p => ∃ n : Nat, p.eval (extend ν n)

def conjunction (xs : List Formula) : Formula := xs.foldr Formula.and .truth

def disjunction (xs : List Formula) : Formula := xs.foldr Formula.or .falsity

/-- A single actual S applied to one ground name, with that name receiving
precisely the supplied encoded input. -/
def successor (a b : Expr) : Formula :=
  .observation (Γ := [.ground]) (by simp) (successorProbe .here) [a] b

/-- Full Phi graph: all four small inputs are present. The only unbounded
branch invokes the literal S source, and its n+4 constraint is branch-local. -/
def phi (a b : Expr) : Formula :=
  .or
    (disjunction ((List.range 4).map fun i =>
      .and (.eq a (.numeral i)) (.eq b (.numeral (Phi i)))))
    (.existsNat (.and (.eq (a.lift 1) (.add (.variable 0) (.numeral 4)))
      (successor (.variable 0) (b.lift 1))))

/-- Exactly d copies of the finite Phi formula. d is a syntactic compiler
parameter, never a runtime witness or an assumed variable-iteration gate. -/
def phiChain : Nat → Expr → Expr → Formula
  | 0, a, b => .eq b a
  | d+1, a, b => .existsNat (.and (phi (a.lift 1) (.variable 0))
      (phiChain d (.variable 0) (b.lift 1)))

/-- Positional shared-input tuple, including unused functional positions. -/
def inputValues {Γ : List Ty} (ν : Nat → Nat) (xs : List Expr) :
    Variable Γ .ground → Nat :=
  fun x => (xs.getD (SourceTypedPorts.variableIndex x) (.numeral 0)).value ν

/-- The exact finite unit-elimination tree is expanded into arithmetic, not
left as a semantic graph atom. Only literal all-ground source leaves remain. -/
def unitFormula {Γ : List Ty} (q : UnitElimination.Tree Nat Γ)
    (xs : List Expr) (r : Expr) : Formula :=
  match q with
  | .leaf b =>
      .existsNat (.existsNat (.existsNat (conjunction [
        .observation (by
          intro σ hσ
          rcases List.mem_cons.mp hσ with rfl | hσ
          · rfl
          · rcases List.mem_cons.mp hσ with rfl | hσ
            · rfl
            · exact b.allGround σ hσ) b.left
          (.variable 2 :: .variable 1 :: xs.map (Expr.lift 3)) (.variable 0),
        .observation (by
          intro σ hσ
          rcases List.mem_cons.mp hσ with rfl | hσ
          · rfl
          · rcases List.mem_cons.mp hσ with rfl | hσ
            · rfl
            · exact b.allGround σ hσ) b.right
          (.variable 2 :: .variable 1 :: xs.map (Expr.lift 3)) (.variable 0),
        .eq (.add (.scale b.factor (r.lift 3)) (.add (.variable 2) (.numeral 1)))
          (.add (.numeral (b.factor*b.anchor)) (.add (.variable 1) (.numeral 1))) ])))
  | .free left _ _ d p =>
      .existsNat (.and
        (unitFormula p ((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 1))
          (.add (.variable 0) (.numeral 1)))
        (.eq (.add (.variable 0) (.numeral 1))
          (.add (.scale (d+1) (r.lift 1)) (.numeral d))))
  | .active left _ _ p d d' c q s =>
      .existsNat (.existsNat (conjunction [
        unitFormula q ((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 2))
          (.add (.variable 1) (.numeral 1)),
        unitFormula s ((xs.take left.length ++ xs.drop (left.length+1)).map (Expr.lift 2))
          (.add (.variable 0) (.numeral 1)),
        .eq (.add (.scale (p*d') (.add (.variable 1) (.numeral 1))) (.numeral (d*c)))
          (.add (.scale d (.add (.variable 0) (.numeral 1)))
            (.scale (p*(d'-d)) (r.lift 2))) ]))

end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.Arithmetic
