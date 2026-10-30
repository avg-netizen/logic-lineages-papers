module
public import LogicLineages.OrdinalComparison.SuccessorMassResidualTargets
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 strict-mass proof725–737: actual equal-global residual cuts.
Generic B and the two-block budget are supplier hypotheses, never a substituted
source threshold. No child strictness or terminal-word oracle is assumed. -/
def ActualSuccessorMassResidualCuts : Prop :=
  ∀ gamma : Ordinal.{0}, 0 < gamma → Ordinal.omega0^gamma*Ordinal.omega0 < epsilonZero →
    ∀ B c e : Nat, c < e → e ≤ B → 2*actualOrdinalNorm (Ordinal.omega0^gamma) ≤ B-e →
      let theta := Ordinal.omega0^gamma
      let L := theta*Ordinal.omega0
      let w := actualOrdinalNorm theta
      let q := (B-e)/w
      let qc := (B-c)/w
      let re := actualMaximumPredecessor theta ((B-e)%w)
      let rc := actualMaximumPredecessor theta ((B-c)%w)
      let rhi := theta*((qc-q : Nat) : Ordinal)+rc
      let Alo := actualMaximumPredecessor L (B-e)
      let Ahi := actualMaximumPredecessor L (B-c)
      let pe := e+q*w
      let pc := c+q*w
      let Ce := actualControlledCount (compensatedPrefixControl pe) re
      let Cc := actualControlledCount (compensatedPrefixControl pc) rhi
      let Ue := (Phi^[Ce]) B
      let Uc := (Phi^[Cc]) B
      Ce ≤ Cc ∧ B ≤ Ue ∧ Ue ≤ Uc ∧
      Ce ≤ actualControlledCount (compensatedPrefixControl e) Alo ∧
      Cc ≤ actualControlledCount (compensatedPrefixControl c) Ahi ∧
      (∀ i : Nat, i ≤ Ce → actualControlledStateAfter (compensatedPrefixControl e) Alo i =
        theta*(q : Ordinal)+actualControlledStateAfter (compensatedPrefixControl pe) re i) ∧
      (∀ i : Nat, i ≤ Cc → actualControlledStateAfter (compensatedPrefixControl c) Ahi i =
        theta*(q : Ordinal)+actualControlledStateAfter (compensatedPrefixControl pc) rhi i) ∧
      pe ≤ Ue ∧ pc ≤ Uc ∧
      actualControlledStateAfter (compensatedPrefixControl e) Alo Ce = theta*(q : Ordinal)+((Ue-pe : Nat) : Ordinal) ∧
      actualControlledStateAfter (compensatedPrefixControl c) Ahi Cc = theta*(q : Ordinal)+((Uc-pc : Nat) : Ordinal)

end LogicLineages.OrdinalComparison.Targets
