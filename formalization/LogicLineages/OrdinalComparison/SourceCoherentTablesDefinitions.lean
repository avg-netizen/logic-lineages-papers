module
public import Mathlib.Order.CompleteSublattice
public import Mathlib.Data.Fintype.Pi
@[expose] public section
/-! A bounded supplier for paper06's lattice induction. Lower-output weakening
homs are actual input data, not closure assumptions about the current family.
Only the finite filter is claimed executable; arbitrary suprema/infima remain
mathematical lattice operations. Recursive source domains are not constructed. -/
namespace LogicLineages.OrdinalComparison.Source.SourceCoherentTables

abbrev Raw (I : Type) (A B : I → Type) := ∀ i, A i → B i

structure Diagram (I : Type) (A B : I → Type) [∀ i, CompleteLattice (B i)] where
  extension : I → I → Bool
  inputMap : ∀ i j, extension i j = true → A i → A j
  outputMap : ∀ i j, extension i j = true → CompleteLatticeHom (B i) (B j)

def Coherent {I : Type} {A B : I → Type} [∀ i, Preorder (A i)]
    [∀ i, CompleteLattice (B i)] (D : Diagram I A B) (f : Raw I A B) : Prop :=
  (∀ i, Monotone (f i)) ∧ ∀ i j, if h : D.extension i j = true then
    ∀ x, D.outputMap i j h (f i x) = f j (D.inputMap i j h x) else True

instance coherentDecidable {I : Type} {A B : I → Type} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) (f : Raw I A B) : Decidable (Coherent D f) := by
  unfold Coherent Monotone
  infer_instance

def validityTest {I : Type} {A B : I → Type} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) (f : Raw I A B) : Bool := decide (Coherent D f)

def finiteTables {I : Type} {A B : I → Type} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)]
    [∀ i, Preorder (A i)] [∀ i, CompleteLattice (B i)]
    [∀ i, DecidableLE (A i)] [∀ i, DecidableLE (B i)]
    (D : Diagram I A B) : Finset (Raw I A B) :=
  Finset.univ.filter fun f => validityTest D f = true

end LogicLineages.OrdinalComparison.Source.SourceCoherentTables
