module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedMultisetCertificate NumberedMulCertificate NumberedUniverseBindingTargets

theorem typedMulCertificates : NumberedMulCertificateTargets.ActualTypedMulCertificates := by
  intro n arity symbols S Gamma q r
  constructor
  · rintro ⟨certificate,h⟩
    obtain ⟨tau,q⟩ := q
    obtain ⟨upsilon,r⟩ := r
    cases q with
    | var => simp [mulCertificateTest] at h
    | lam => simp [mulCertificateTest] at h
    | app => simp [mulCertificateTest] at h
    | bottom => simp [mulCertificateTest] at h
    | ordinary => simp [mulCertificateTest] at h
    | numbered k f tau base types extras =>
      cases k with
      | zero => simp [mulCertificateTest] at h
      | succ k =>
        cases r with
        | var => simp [mulCertificateTest] at h
        | lam => simp [mulCertificateTest] at h
        | app => simp [mulCertificateTest] at h
        | bottom => simp [mulCertificateTest] at h
        | numbered => simp [mulCertificateTest] at h
        | ordinary g target =>
          have hh : (tau=headResult g ∧ RecursiveComparison.headEquivalent f g ∧ HeadInWindow arity symbols S g) ∧
              multisetTest (argumentList base) (argumentList target) certificate=true := by
            simpa [mulCertificateTest] using h
          obtain ⟨⟨ht,he,hw⟩,hm⟩ := hh
          cases ht
          exact .mul k f g base types extras target he hw
            ((NumberedMultisetCertificateProof.primitiveMultisetCertificates n arity Gamma _ _).mp ⟨certificate,hm⟩)
  · intro h
    cases h with
    | mul k f g base types extras target he hw hm =>
      obtain ⟨certificate,hc⟩ := (NumberedMultisetCertificateProof.primitiveMultisetCertificates n arity Gamma _ _).mpr hm
      exact ⟨certificate,by simp [mulCertificateTest,he,hw,hc]⟩

theorem typedMulSound : NumberedMulCertificateTargets.ActualTypedMulSound := by
  intro n arity symbols S Gamma above q r certificate h hq
  have hi := (typedMulCertificates n arity symbols S Gamma q r).mp ⟨certificate,h⟩
  cases hi with
  | mul k f g base types extras target he hw hm =>
    have hb : GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) base := ⟨hq.1.2.1,hq.2.2.1⟩
    have hsource := (NumberedUniverseOperationsProof.actualArgumentOccurrences (Fin n) arity
      (fun t => t∈S) (HeadInWindow arity symbols S) Gamma _ base).mp hb
    have htarget := NumberedUniverseOperationsProof.actualPrimitiveMultiset (Fin n) arity
      (fun t => t∈S) (HeadInWindow arity symbols S) Gamma _ _ hm hsource
    have ha := (NumberedUniverseOperationsProof.actualArgumentOccurrences (Fin n) arity
      (fun t => t∈S) (HeadInWindow arity symbols S) Gamma _ target).mpr htarget
    refine ⟨?_,headResult g,_,_,rfl,rfl,.mul k f g base types extras target he hm hw⟩
    exact ⟨⟨hq.1.1,ha.1⟩,hw,ha.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateProof
