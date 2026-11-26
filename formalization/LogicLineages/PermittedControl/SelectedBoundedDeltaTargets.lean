module
public import LogicLineages.PermittedControl.SelectedBoundedDeltaDefinitions
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoundedDeltaTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFirstFree SelectedBoundedDelta Source.AdmissibleSum

/-- Compositional supplier only: an explicitly supplied first-free endpoint
budget bounds positive partial outputs. The global theorem below must pay
this premise from original bounded input vectors, not assume it. -/
def PartialNormFromFreeBudget : Prop :=
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade ctrl Γ σ i t → ∀ (ρ : AdmissibleSubstitution ctrl Γ) (C : Nat), 0 < C →
    (∀ (k : Nat) (u : OrdinalExpression (σ :: Γ)), FirstFree Γ σ i t k u → 0 < k →
      actualOrdinalNorm (expressionValue ctrl ρ (ordinalHeadClosure u)) ≤ C) →
    ∀ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p i t = some v →
      ∀ j, 0 < j.val → actualOrdinalNorm (expressionValue ctrl ρ (v j)) ≤ ordinalPartialSize t * (2 * C)

/-- Actual positive partial bound used by thm:delta-bounded-norm. The scalar output w
is constrained by the actual root partial equation. All endpoint budgets are
proved from bounded original input, with the unchanged factor2^n. -/
def VectorPartialNorm : Prop :=
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade ctrl Γ σ i.val (h i)) → BoundedVector ctrl h →
    ∀ (ρ : AdmissibleSubstitution ctrl Γ) (w : OrdinalPartialVector Γ σ),
      AdmissiblePartial.run p 0 (h 0) = some w →
      ∀ (i : Fin (m + 1)) (v : OrdinalPartialVector Γ σ),
        AdmissiblePartial.run p i.val (h i) = some v →
        ∀ j, 0 < j.val → actualOrdinalNorm (expressionValue ctrl ρ (v j)) ≤
          ordinalPartialSize (h i) *
            (2 ^ (σ.level + 1) * finiteValue (expressionValue ctrl ρ (w 0)))

def BoundedVectorSupportBridge : Prop :=
  ∀ (ctrl : Nat → Nat) (Γ : List Ty) (m : Nat) (h : OrdinalVector Γ m), BoundedVector ctrl h ↔ SourceBoundedVector ctrl h

/-- Whole repaired Paper17 thm:delta-bounded-norm. The actual delta definition retains the
original multiplier2^(level(X)+1)*sum(partialSize). Original C^X input and
occurring-vector bounded substitutions are retained verbatim; no free-subtree,
positive-partial, scalar weakness or product/exponential estimate is assumed. -/
def DeltaPreservesBoundedNorm : Prop :=
  ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade ctrl Γ σ i.val (h i)) → SourceBoundedVector ctrl h →
    ∃ v : OrdinalVector Γ (max (σ.level + 1) m), LiteralCovariance.delta p h = some v ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v

/-- Actual source scalar output, with the unchanged literal multiplier. -/
def DeltaScalarNorm : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade ctrl Γ σ i.val (h i)) →
    ∀ (v : OrdinalVector Γ (max (σ.level + 1) m)) (w : OrdinalPartialVector Γ σ),
      LiteralCovariance.delta p h = some v → AdmissiblePartial.run p 0 (h 0) = some w →
      ∀ ρ : AdmissibleSubstitution ctrl Γ,
        actualOrdinalNorm (expressionValue ctrl ρ (v 0)) =
          (2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum) *
            finiteValue (expressionValue ctrl ρ (w 0))

def FullSelectedBoundedDelta : Prop := BoundedVectorSupportBridge ∧
  PartialNormFromFreeBudget ∧ VectorPartialNorm ∧ DeltaScalarNorm ∧ DeltaPreservesBoundedNorm

end LogicLineages.PermittedControl.SelectedBoundedDeltaTargets
