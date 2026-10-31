module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedScottCompleteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Full source reduced classification: actual unique length, calibrated
terminal multiplicities, exhaustive rows and explicit unrestricted raw endpoints.
No classification, realization, Scott sentence or comparison is an input. -/
def reducedScottFullSource : Prop :=
  (∀ (G:Type) [AddCommGroup G] [Countable G] [Nontrivial G] (p:ℕ) [Fact p.Prime],
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G →
    (∃! z:Ordinal.{0}×ℕ, Countable z.1.ToType ∧ PGroupExactLength p G (Ordinal.omega0*z.1+z.2)) ∧
    ∀ (γ:Ordinal.{0}) [Countable γ.ToType] (N:ℕ),
      PGroupExactLength p G (Ordinal.omega0*γ+N) →
      (N=0 → 0<γ ∧ RawPiEndpoint G (2*γ+1) ∧ NoRawDifference G (2*γ)) ∧
      (0<N → let H := (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G);
        (∃I:Fin N→Type, Nonempty (H≃+CyclicRootSum p N I) ∧
          (∀j:Fin N, Cardinal.mk (I j)=TerminalRank p H j.val) ∧
          (∀j:Fin N, Cardinal.mk (I j)≤Cardinal.aleph0) ∧
          (∀j:Fin N, j.val=N-1 → Cardinal.mk (I j)≠0)) ∧
        (Finite H ∨ (∃k:ℕ, OneInfiniteTerminal p H N k) ∨ TwoInfiniteTerminal p H N) ∧
        (Finite H → RawDifferenceEndpoint G (2*γ+1)) ∧
        (∀k:ℕ, OneInfiniteTerminal p H N k →
          ((∀j:ℕ, j<k-1 → TerminalRank p H j=0) → RawPiEndpoint G (2*γ+2)) ∧
          ((∃j:ℕ, j<k-1 ∧ TerminalRank p H j≠0) → RawDifferenceEndpoint G (2*γ+2))) ∧
        (TwoInfiniteTerminal p H N → RawPiEndpoint G (2*γ+3) ∧ NoRawDifference G (2*γ+2)))) ∧
  (∀ (G:Type) [AddCommGroup G] [Subsingleton G],
    (∃φ:Formula 0, Complexity .pi (1:Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ) ∧
    (∀q:QF 0, ¬ RawScottSentence (RawGroupStructure.ofGroup G) (Formula.qf q)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
