module
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Entire source paper07 lem:oneinput on genuine finite one-variable collected
forms. Computation is on faithful numeric syntax, not a peak-order oracle. -/
def FullActualCollectedOneInput : Prop :=
  Primrec encodedCollectedFamilyThreshold ∧
  ∀ forms : List CollectedPositiveNF, (∀ A∈forms, CollectedPositiveValid A) →
    let N := encodedCollectedFamilyThreshold (forms.map collectedPositiveEncode)
    N=collectedFamilyThreshold forms ∧ 1≤N ∧
    ∀ x : Nat, N≤x →
      (∀ (rho : NONote) (c b : Nat) (tags : CollectedPositiveTags),
        (rho,CollectedPositiveNF.mk c b tags)∈collectedFamilyTags forms →
        let t := actualOrdinalNorm (actualCollectedTagInput rho (.mk c b tags) x)
        (tags=.nil → x≤t ∧ t<Phi x) ∧ (tags≠.nil → ControlRoot t ∧ Phi x<t)) ∧
      (∀ (rho sigma : NONote) (A B : CollectedPositiveNF),
        (rho,A)∈collectedFamilyTags forms → (sigma,B)∈collectedFamilyTags forms →
        actualCollectedTagPeak rho A x=actualCollectedTagPeak sigma B x →
        rho=sigma ∧ actualCollectedPositiveEval A x=actualCollectedPositiveEval B x)

end LogicLineages.OrdinalComparison.Targets
