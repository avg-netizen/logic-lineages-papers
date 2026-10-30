module
public import LogicLineages.OrdinalComparison.RepeatedWordOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Genuine successor induction step for paper07 (7.5). The child induction
proposition and two-block numerical budget are explicit local premises; the
whole source theorem must discharge them using its computed threshold. -/
def ActualSuccessorKernelStrictMassStep : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr →
    Ordinal.omega0^eta.1.repr*Ordinal.omega0 < epsilonZero → ∀ S : Nat,
    ((Ordinal.omega0^eta.1.repr=Ordinal.omega0^(2 : Ordinal) ∧ S=0) ∨
      (Ordinal.omega0^(3 : Ordinal) ≤ Ordinal.omega0^eta.1.repr ∧
        actualKernelStrictMassAt (Ordinal.omega0^eta.1.repr) S)) →
    ∀ t c e : Nat, S ≤ t → c < e →
      e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr*Ordinal.omega0) ≤ t →
      2*actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ Phi t-e →
      actualSuffixKernel (Ordinal.omega0^eta.1.repr*Ordinal.omega0) e t <
        actualSuffixKernel (Ordinal.omega0^eta.1.repr*Ordinal.omega0) c t

end LogicLineages.OrdinalComparison.Targets
