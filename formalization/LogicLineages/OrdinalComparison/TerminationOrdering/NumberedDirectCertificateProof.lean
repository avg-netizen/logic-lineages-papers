module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedDirectCertificate

theorem directRuleCheck : NumberedDirectCertificateTargets.ActualDirectRuleCheck := by
  intro n arity Gamma rule q r
  constructor
  · intro h
    obtain ⟨tau,q⟩ := q
    cases rule with
    | put label =>
      cases q with
      | ordinary f base => cases h; exact .put label f base
      | var => simp [directTarget] at h
      | lam => simp [directTarget] at h
      | app => simp [directTarget] at h
      | bottom => simp [directTarget] at h
      | numbered => simp [directTarget] at h
    | abstraction =>
      cases q with
      | numbered k f tau base types extras =>
        cases k with
        | zero => simp [directTarget] at h
        | succ k =>
          cases tau with
          | ground => simp [directTarget] at h
          | arrow sigma tau => cases h; exact .abstraction k f sigma tau base types extras
      | var => simp [directTarget] at h
      | lam => simp [directTarget] at h
      | app => simp [directTarget] at h
      | bottom => simp [directTarget] at h
      | ordinary => simp [directTarget] at h
    | beta =>
      unfold directTarget at h
      split at h <;> try contradiction
      next output sigma body a heRule hePack =>
        cases h
        rw [hePack]
        exact .beta sigma output body a
    | bottom =>
      cases q <;> simp only [directTarget] at h
      all_goals first | contradiction | (cases h; exact .bottom _ _ (by intro he; cases he))
  · intro h
    cases h with
    | put => rfl
    | abstraction => rfl
    | beta => rfl
    | bottom tau q hn => cases q <;> simp_all [directTarget]

theorem directRuleSound : NumberedDirectCertificateTargets.ActualDirectRuleSound := by
  intro n arity symbols S hc Gamma above rule q r h hq
  have hi := (directRuleCheck n arity Gamma rule q r).mp h
  have hs : ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),q=⟨tau,a⟩ ∧ r=⟨tau,b⟩ ∧
      WindowStep (Fin n) arity symbols S above Gamma tau a b := by
    cases hi with
    | put label f base => exact ⟨_,_,_,rfl,rfl,.put label f base⟩
    | abstraction k f sigma tau base types extras => exact ⟨_,_,_,rfl,rfl,.abs k f base types extras⟩
    | beta sigma tau body a => exact ⟨_,_,_,rfl,rfl,.beta body a⟩
    | bottom tau q hn => exact ⟨_,_,_,rfl,rfl,.bottom q hn⟩
  obtain ⟨tau,a,b,rfl,rfl,hs⟩ := hs
  exact ⟨NumberedWindowReductionProof.stepGood symbols S hc hs hq,tau,a,b,rfl,rfl,hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateProof
