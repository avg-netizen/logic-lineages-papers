module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerPrintedTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalBasisTargets

@[expose] public section

/-! # The tower sequence (D) of Paper 16, ordinals.tex 564–590, its native terms and semantic composites

Printed: `N_B = B_1 B_0 Next`, `ε_B = Γ_0 = N_B(ω)`, and
`Δ_0 = Γ_0`, `Δ_1 = N_B Γ_0`, `Δ_{l+2} = B_l B_{l-1} ⋯ B_0 N_B Γ_0`;
"Replace the operations in (D) by their native realizers and call the resulting closed terms t_n."

The native realizers are: `B_l ↦ towerTerm fix l` (#1459), `Next = fix pow ↦ ordinalNext`,
`ω ↦ w = Cap(s,Z) = omegaCarrier` (#1456 closure). As a term, `Γ_0` is the composite `N_B(ω)`;
its equality with the Veblen ordinal Γ_0 is Simmons's identity (external) and is NOT used:
`Δ_n'` below is the paper's composite of the semantic `B_l`, `Next = fix pow` and `ω = w`,
not its identification with ψ_B(a_n). -/

namespace LogicLineages.PersistentMarking.NativeTowerSequenceTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets

/-! Native terms. -/

/-- The native `B_l` with the printed `fix`. -/
def towerB (l : Nat) : Expr := towerTerm NativeOrdinalExponentialTargets.ordinalFix l

/-- `v B_{k-1} ⋯ B_0` for `v : |A_{k+2}|`. -/
def downTerm : Nat → Expr → Expr
  | 0, v => v
  | k + 1, v => downTerm k (app (tierType (k+2)) (tierType (k+2)) v (towerB k))

/-- `N_B = B_1 B_0 Next`. -/
def veblenTerm : Expr :=
  app (tierType 1) (tierType 1) (app (tierType 2) (tierType 2) (towerB 1) (towerB 0))
    NativeOrdinalExponentialTargets.ordinalNext

/-- `ε_B = N_B(ω)`, printed `Γ_0`. -/
def baseTerm : Expr := app indexType indexType veblenTerm NativeOrdinalBasisTargets.omegaCarrier

/-- The closed native terms `t_n` of (D). -/
def sequenceTerm : Nat → Expr
  | 0 => baseTerm
  | 1 => app indexType indexType veblenTerm baseTerm
  | l + 2 => app indexType indexType
      (app (tierType 1) (tierType 1) (downTerm l (towerB l)) veblenTerm) baseTerm

/-! Semantic composites, from the semantic `fix`, `pow` and `w`. -/

/-- `v B_{k-1} ⋯ B_0` semantically, `B_j = towerValue fix j`. -/
noncomputable def downValue (fix : Value (tier 2)) : (k : Nat) → Value (tier (k+2)) → Value (tier 2)
  | 0, v => v
  | k + 1, v => downValue fix k (v (towerValue fix k))

/-- `N_B = B_1 B_0 Next` with `Next = fix pow`. -/
noncomputable def veblenValue (fix : Value (tier 2)) (pow : Value (tier 1)) : Value (tier 1) :=
  towerValue fix 1 (towerValue fix 0) (fix pow)

/-- `ε_B = N_B(ω)`. -/
noncomputable def baseValue (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) :
    CountableOrdinal :=
  veblenValue fix pow w

/-- The paper's composites `Δ_n'`. -/
noncomputable def sequenceValue (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) :
    Nat → CountableOrdinal
  | 0 => baseValue fix pow w
  | 1 => veblenValue fix pow (baseValue fix pow w)
  | l + 2 => downValue fix l (towerValue fix l) (veblenValue fix pow) (baseValue fix pow w)

/-- Each `t_n` is closed native of type σ and realizes `Δ_n'`; at ι this says
`r_σ(t_n) ≥ Δ_n'`. -/
def NativeTowerSequenceRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
      (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
      (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
      (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
      OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
      ∀ n, ∃ t : (nativeTerms S).term .base, t.val = sequenceTerm n ∧
        Realizes (nativeTerms S) wf .base t (sequenceValue fix pow w n)

end LogicLineages.PersistentMarking.NativeTowerSequenceTargets
