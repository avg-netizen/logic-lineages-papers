module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.TerminalMultiplicityDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.RawScottDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
/-- Explicit raw upper and same-level Sigma exclusion, not an input oracle. -/
def RawPiEndpoint (G:Type) [AddCommGroup G] (α:Ordinal.{0}) : Prop :=
  (∃φ:Formula 0, Complexity .pi α φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
  (∀φ:Formula 0, Complexity .sigma α φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ)
def RawDifferenceEndpoint (G:Type) [AddCommGroup G] (α:Ordinal.{0}) : Prop :=
  (∃d:DifferenceFormula 0, d.AtLevel α ∧ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d) ∧
  (∀φ:Formula 0, Complexity .sigma α φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
  (∀φ:Formula 0, Complexity .pi α φ → ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ)
def NoRawDifference (G:Type) [AddCommGroup G] (α:Ordinal.{0}) : Prop :=
  ∀d:DifferenceFormula 0, d.AtLevel α → ¬ RawDifferenceScottSentence (RawGroupStructure.ofGroup G) d
noncomputable def TerminalRank (p:ℕ) (H:Type) [AddCommGroup H] (j:ℕ) : Cardinal :=
  Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j:AddSubgroup H))
def OneInfiniteTerminal (p:ℕ) (H:Type) [AddCommGroup H] (N k:ℕ) : Prop :=
  0<k ∧ k≤N ∧ TerminalRank p H (k-1)=Cardinal.aleph0 ∧
    ∀j:ℕ, j<N → j≠k-1 → TerminalRank p H j<Cardinal.aleph0
def TwoInfiniteTerminal (p:ℕ) (H:Type) [AddCommGroup H] (N:ℕ) : Prop :=
  ∃a b:Fin N, a<b ∧ TerminalRank p H a.val=Cardinal.aleph0 ∧ TerminalRank p H b.val=Cardinal.aleph0
end LogicLineages.ModelsAlgebra.PGroups
