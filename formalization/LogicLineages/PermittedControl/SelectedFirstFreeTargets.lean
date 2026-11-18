module
public import LogicLineages.PermittedControl.SelectedFirstFreeDefinitions
public import LogicLineages.PermittedControl.SelectedWeakScalarTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFirstFreeTargets
open OrdinalComparison Source SelectedSourceDomain SelectedFirstFree

def AddChildNorm : Prop :=
  ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ) (i : Nat) (f g : OrdinalExpression Γ),
    AmbientGrade ctrl Γ i f → AmbientGrade ctrl Γ i g →
    actualOrdinalNorm (expressionValue ctrl ρ f) ≤ actualOrdinalNorm (expressionValue ctrl ρ (.add f g)) ∧
    actualOrdinalNorm (expressionValue ctrl ρ g) ≤ actualOrdinalNorm (expressionValue ctrl ρ (.add f g))

def ExpChildNorm : Prop :=
  ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ) (i : Nat) (f g : OrdinalExpression Γ),
    0 < i → AmbientGrade ctrl Γ (i + 1) f → AmbientGrade ctrl Γ i g →
    actualOrdinalNorm (expressionValue ctrl ρ f) ≤ 2 * actualOrdinalNorm (expressionValue ctrl ρ (.emul f g)) ∧
    actualOrdinalNorm (expressionValue ctrl ρ g) ≤ actualOrdinalNorm (expressionValue ctrl ρ (.emul f g))

def CollapseChildNorm : Prop :=
  ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ) (f g : OrdinalExpression Γ),
    AmbientGrade ctrl Γ 1 f → AmbientGrade ctrl Γ 0 g →
    actualOrdinalNorm (expressionValue ctrl ρ f) ≤ actualOrdinalNorm (expressionValue ctrl ρ (.collapse f g)) ∧
    actualOrdinalNorm (expressionValue ctrl ρ g) ≤ actualOrdinalNorm (expressionValue ctrl ρ (.collapse f g))

def FirstFreeEndpoint : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i j : Nat) (t u : OrdinalExpression (σ :: Γ)),
    FirstFree Γ σ i t j u → ordinalHeadFree u = true

def FirstFreeGrade : Prop :=
  ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (i j : Nat) (t u : OrdinalExpression (σ :: Γ)),
    HeadGrade ctrl Γ σ i t → FirstFree Γ σ i t j u → HeadGrade ctrl Γ σ j u

/-- Complete Paper17 lem:first-free-subtree. Here n=level(X)+1, so the multiplier is
2^(n-1), not the later larger 2^n. The scalar B is interpreted by its proved
finite value; no output-closure norm or path bound is assumed. -/
def FirstFreeBound : Prop :=
  ∀ (ctrl : Nat → Nat) (B : Nat), SelectedWithThreshold ctrl B →
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade ctrl Γ σ i.val (h i)) → BoundedVector ctrl h →
    ∀ (ρ : AdmissibleSubstitution ctrl Γ) (i : Fin (m + 1)) (j : Nat)
      (u : OrdinalExpression (σ :: Γ)), FirstFree Γ σ i.val (h i) j u → 0 < j →
      actualOrdinalNorm (expressionValue ctrl ρ (ordinalHeadClosure u)) ≤
        2 ^ σ.level * finiteValue (expressionValue ctrl ρ (ordinalHeadClosure (h 0)))

/-- Dropping and then weakening the tracked context changes no free endpoint tree. -/
def FreeReconstruction : Prop := ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
  ordinalHeadFree t = true → LiteralCovariance.weaken σ (ordinalHeadClosure t) = t

def FullSelectedFirstFree : Prop := AddChildNorm ∧ ExpChildNorm ∧ CollapseChildNorm ∧
  FirstFreeEndpoint ∧ FirstFreeGrade ∧ FirstFreeBound ∧ FreeReconstruction ∧
  SelectedWeakScalarTargets.SupportComparisonBridge

end LogicLineages.PermittedControl.SelectedFirstFreeTargets
