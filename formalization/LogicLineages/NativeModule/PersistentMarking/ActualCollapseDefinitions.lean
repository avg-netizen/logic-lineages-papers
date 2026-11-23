module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSequenceTargets
public import LogicLineages.PersistentMarking.ActualOmegaTowerDefinitions
public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

@[expose] public section

/-! # An actual collapse for Paper 16's tower (ordinals.tex 593–610)

Printed: "an N_B-critical ordinal is an orbit value N_B^α(Γ_0)"; "ψ_B(ξ) [is] the least such
critical θ for which η<ξ, |η|<θ ⟹ ψ_B(η)<θ (P)"; "The coefficient norm is recursively the maximum
of the countable coefficients in the base-Ω representation and of the norms of its exponents."

- Indices: ordinals `ξ ≤ Λ` (`Λ = ActualOmegaTower.endpoint = sup_n a_n`, #1479), the range on
  which the hereditary base-Ω representation terminates (every `0 < η < Λ` has its exponents
  below `η`).
- Values: `Ordinal.{0}`; all values that occur are proved `< ω₁` in the proof modules.
- `N_B` and `Γ_0` are the repository's semantic `veblenValue fix pow` and `baseValue fix pow w`
  (#1462) for a solution of the arithmetic and ω equations; orbits are the full-prefix orbits
  `OrdinalNativeOrbitProof.orbit` of convention (I).
- `ψ` is defined by well-founded recursion as the least critical `θ` satisfying the clause
  ("the defining clause of this particular collapse"). -/

namespace LogicLineages.PersistentMarking.ActualCollapse
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open OrdinalNativeOrbitProof NativeTowerTargets NativeTowerSequenceTargets

/-- The coefficient norm: the maximum over the base-Ω Cantor normal form of the coefficients and
of the norms of the exponents. (An exponent equal to the ordinal itself, which happens only at
fixed points `Ω^η = η`, i.e. never below `Λ`, contributes 0.) -/
noncomputable def coefficientNorm (o : Ordinal.{0}) : Ordinal.{0} :=
  ((CNF omegaIndex o).map (fun p => max p.2 (if h : p.1 < o then coefficientNorm p.1 else 0))).foldr max 0
termination_by o
decreasing_by exact h

/-- `N`-critical: an orbit value `N^α(Γ)` (convention (I)). -/
def Critical (N : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal) (θ : Ordinal.{0}) : Prop :=
  ∃ α : CountableOrdinal, (orbit .base N Γ α).val = θ

/-- The index order: ordinals up to the endpoint `Λ`. -/
abbrev ActualIndex : Type 1 := {ξ : Ordinal.{0} // ξ ≤ endpoint}

/-- The least critical value satisfying the clause (P) over the earlier values. -/
noncomputable def collapse {I : Type*} [LinearOrder I] [WellFoundedLT I]
    (norm : I → Ordinal.{0}) (critical : Ordinal.{0} → Prop) : I → Ordinal.{0} :=
  (wellFounded_lt (α := I)).fix
    (fun ξ prev => sInf {θ | critical θ ∧ ∀ η (h : η < ξ), norm η < θ → prev η h < θ})

noncomputable def actualNorm (ξ : ActualIndex) : Ordinal.{0} := coefficientNorm ξ.val

noncomputable def actualArgument (n : Nat) : ActualIndex :=
  ⟨argument n, Ordinal.le_iSup (fun m => argument m) n⟩

noncomputable def actualEndpoint : ActualIndex := ⟨endpoint, le_rfl⟩

/-- The actual collapse data for critical class `Critical N Γ`. -/
noncomputable def actualData (N : CountableOrdinal → CountableOrdinal) (Γ : CountableOrdinal) :
    CollapseData ActualIndex Ordinal.{0} where
  psi := collapse actualNorm (Critical N Γ)
  norm := actualNorm
  critical := Critical N Γ
  one := 1
  endpoint := actualEndpoint
  a := actualArgument

/-- The paper's instance: `N_B = B_1 B_0 Next` and `Γ_0 = N_B(ω)` (#1462). -/
noncomputable def veblenData (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal) (w : CountableOrdinal) :
    CollapseData ActualIndex Ordinal.{0} :=
  actualData (veblenValue fix pow) (baseValue fix pow w)

end LogicLineages.PersistentMarking.ActualCollapse
