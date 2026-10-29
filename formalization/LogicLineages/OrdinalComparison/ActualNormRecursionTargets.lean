module
public import LogicLineages.OrdinalComparison.OrdinalRepresentationTargets
public import Mathlib.SetTheory.Ordinal.CantorNormalForm

public import Mathlib.SetTheory.Cardinal.ToNat

@[expose] public section

/-! Independent actual-ordinal additive-norm specification.

Paper 05, `foundations.tex`, lines 51–70, especially `def:norm`. The full CNF
coefficient, converted through its finite cardinal, is charged, not its bit length. These targets import neither the
actual norm implementation nor any new norm property proof. Uniqueness is
restricted to the source domain below epsilon zero, leaving outside values
unconstrained. Notation correspondence is a separate mathematical obligation.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualNormCNFEquation (N : Ordinal.{0} → Nat) : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero →
    N a = ((Ordinal.CNF Ordinal.omega0 a).map
      (fun p => p.2.card.toNat * (1 + N p.1))).sum

def ActualNormUniqueBelowEpsilonZero (N : Ordinal.{0} → Nat) : Prop :=
  ∀ M : Ordinal.{0} → Nat, ActualNormCNFEquation M →
    ∀ a : Ordinal.{0}, a < epsilonZero → M a = N a

def ActualNormNotationCorrespondence (N : Ordinal.{0} → Nat) : Prop :=
  ∀ a : NONote, N a.1.repr = Vendor.R1.treeWeight a.1

end LogicLineages.OrdinalComparison.Targets
