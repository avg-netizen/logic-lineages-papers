module
public import LogicLineages.PermittedControl.EqualGapCertificateDefinitions
public import LogicLineages.PermittedControl.GapInputDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Semantic finite threshold retaining both constructed partners. This is
not yet an implementation of ordinal endpoint construction on raw codes. -/
noncomputable def inverseTableTail (lambda mu nu delta : NONote) (B : Nat) : Nat :=
  let kappa := mu.1.repr + delta.1.repr
  let lambdaQ := nu.1.repr + delta.1.repr
  1 + max (max 2 (max (actualOrdinalNorm lambda.1.repr)
    (max (actualOrdinalNorm kappa) (actualOrdinalNorm mu.1.repr))))
    (max (gapInputTail kappa mu.1.repr lambdaQ nu.1.repr 0)
      (max (gapInputTail lambdaQ nu.1.repr kappa mu.1.repr 0)
        (equalGapCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1)
          (rawNoteEncode delta.1) B)))

/-- The printed table compares Q(y) against P(x); code 1 is source sign 0,
code 2 is source sign +1, and code 0 is source sign -1. -/
def InverseTableRows (sign y h valueQ valueP : Nat) : Prop :=
  (sign=1 → ((valueQ<valueP ↔ y<h) ∧ (valueQ=valueP ↔ y=h) ∧
    (valueP<valueQ ↔ h<y))) ∧
  (sign=2 → ((valueQ<valueP ↔ y≤h) ∧ valueQ≠valueP ∧
    (valueP<valueQ ↔ h+1≤y))) ∧
  (sign=0 → ((valueQ<valueP ↔ y≤h-1) ∧ valueQ≠valueP ∧
    (valueP<valueQ ↔ h≤y)))

end LogicLineages.PermittedControl
