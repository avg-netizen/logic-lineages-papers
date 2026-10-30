module

public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchTargets
public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeProof

/-! Proofs of the fixed finite-certificate/search semantics for paper 03.
The search is partial on positive instances; Carter's positive decision
procedure is neither a premise nor a claimed conclusion. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CertificateSearchProof

open FiniteCode CertificateSearch

theorem certificateCodecFaithful : Targets.CertificateCodecFaithful := by
  constructor <;> intro x <;> exact Encodable.encodek x

theorem certificateFamilyValidation : Targets.CertificateFamilyValidation := by
  intro U
  simp [familyValidTest]

theorem permitted_valid {U : Input} {c : Code}
    (h : permittedTest U c = true) : valid c = true :=
  (FiniteCodeProof.valid_iff c).mpr (of_decide_eq_true h).1

theorem certificateVerification : Targets.CertificateVerification := by
  intro U t
  constructor
  · intro ht
    obtain ⟨⟨hfamily, hlist⟩, hneg⟩ :=
      (show (familyValidTest U = true ∧
        decide (t.2.2 = hostCodes (t.1.1 + t.2.1.1)) = true) ∧
        negativePairTest U t.1 t.2.1 = true from
          by simpa only [verify, Bool.and_eq_true] using ht)
    have hU := (certificateFamilyValidation U).mp hfamily
    have hb := hneg
    simp only [negativePairTest, Bool.and_eq_true] at hb
    have hc := permitted_valid hb.1.1
    have hd := permitted_valid hb.1.2
    obtain ⟨hF, hG, hHost⟩ :=
      (FiniteCodeProof.forestNegativePairTestCorrect U hU t.1 t.2.1 hc hd).mp hneg
    exact ⟨hU, hc, hd, of_decide_eq_true hlist, hF, hG, hHost⟩
  · rintro ⟨hU, hc, hd, hlist, hF, hG, hHost⟩
    have hn :=
      (FiniteCodeProof.forestNegativePairTestCorrect U hU t.1 t.2.1 hc hd).mpr
        ⟨hF, hG, hHost⟩
    simpa only [verify, Bool.and_eq_true, decide_eq_true_eq] using
      And.intro (And.intro ((certificateFamilyValidation U).mpr hU) hlist) hn

theorem atIndex_eq_some_iff (U : Input) (n : ℕ) (t : Certificate) :
    atIndex U n = some t ↔
      familyValidTest U = true ∧ ∃ p : Code × Code,
        Encodable.decode n = some p ∧ negativePairTest U p.1 p.2 = true ∧
        makeCertificate p.1 p.2 = t := by
  by_cases hf : familyValidTest U = true
  · cases hd : (Encodable.decode n : Option (Code × Code)) with
    | none =>
      simp only [atIndex, if_pos hf, hd, Option.bind_none, reduceCtorEq, false_and,
        exists_false, and_false]
    | some p =>
      by_cases hn : negativePairTest U p.1 p.2 = true
      · simp only [atIndex, hf, hd, Option.bind_some, hn, ite_true,
          Option.some.injEq, true_and, exists_eq_left']
      · simp only [atIndex, hf, hd, Option.bind_some, hn, ite_true, ite_false,
          Option.some.injEq, reduceCtorEq, false_and, exists_eq_left', exists_false, and_false]
  · simp only [atIndex, hf, ite_false, reduceCtorEq, false_and]

theorem verify_makeCertificate {U : Input} {c d : Code}
    (hf : familyValidTest U = true) (hn : negativePairTest U c d = true) :
    verify U (makeCertificate c d) = true := by
  simp [verify, makeCertificate, hf, hn]

theorem certificateSearchOutputSound : Targets.CertificateSearchOutputSound := by
  intro U t ht
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec ht
  obtain ⟨hf, p, _, hp, he⟩ := (atIndex_eq_some_iff U n t).mp (Option.mem_def.mp hn)
  rw [← he]
  exact verify_makeCertificate hf hp

theorem certificateExistence : Targets.CertificateExistence := by
  classical
  intro U hU
  constructor
  · rintro ⟨t, ht⟩ hJEP
    obtain ⟨_, hc, hd, _, hF, hG, hNoHost⟩ := (certificateVerification U t).mp ht
    exact hNoHost (hJEP (toForest t.1 hc) (toForest t.2.1 hd) hF hG)
  · intro hJEP
    obtain ⟨F, G, hF, hG, hNoHost⟩ :=
      (show ∃ F G : FiniteOrderForest,
        AvoidsForbidden (toFamily U hU) F.Carrier ∧
        AvoidsForbidden (toFamily U hU) G.Carrier ∧
        ¬ ∃ H : FiniteOrderForest, AvoidsForbidden (toFamily U hU) H.Carrier ∧
          Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier) from
        by simpa only [HasJEP, not_forall, Classical.not_imp, exists_prop] using hJEP)
    let c := FiniteCodeProof.canonicalCode F
    let d := FiniteCodeProof.canonicalCode G
    have hc : valid c = true := FiniteCodeProof.canonical_valid F
    have hd : valid d = true := FiniteCodeProof.canonical_valid G
    let eF := FiniteCodeProof.canonicalIso F
    let eG := FiniteCodeProof.canonicalIso G
    have hFc : AvoidsForbidden (toFamily U hU) (toForest c hc).Carrier :=
      HostReductionProof.forbiddenAvoidanceHereditary _ _ _ eF.symm.toOrderEmbedding hF
    have hGd : AvoidsForbidden (toFamily U hU) (toForest d hd).Carrier :=
      HostReductionProof.forbiddenAvoidanceHereditary _ _ _ eG.symm.toOrderEmbedding hG
    have hNo : ¬ ∃ H : FiniteOrderForest, AvoidsForbidden (toFamily U hU) H.Carrier ∧
        Nonempty ((toForest c hc).Carrier ↪o H.Carrier) ∧
        Nonempty ((toForest d hd).Carrier ↪o H.Carrier) := by
      rintro ⟨H, hH, ⟨f⟩, ⟨g⟩⟩
      exact hNoHost ⟨H, hH, ⟨eF.toOrderEmbedding.trans f⟩, ⟨eG.toOrderEmbedding.trans g⟩⟩
    have hn := (FiniteCodeProof.forestNegativePairTestCorrect U hU c d hc hd).mpr
      ⟨hFc, hGd, hNo⟩
    exact ⟨makeCertificate c d,
      verify_makeCertificate ((certificateFamilyValidation U).mpr hU) hn⟩

theorem certificateSearchDomain : Targets.CertificateSearchDomain := by
  intro U hU
  rw [← certificateExistence U hU]
  constructor
  · intro h
    exact ⟨(search U).get h, certificateSearchOutputSound U _ (Part.get_mem h)⟩
  · rintro ⟨t, ht⟩
    obtain ⟨_, hc, hd, _, hF, hG, hNo⟩ := (certificateVerification U t).mp ht
    have hn :=
      (FiniteCodeProof.forestNegativePairTestCorrect U hU t.1 t.2.1 hc hd).mpr
        ⟨hF, hG, hNo⟩
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Encodable.encode (t.1, t.2.1), makeCertificate t.1 t.2.1, ?_⟩
    apply Option.mem_def.mpr
    apply (atIndex_eq_some_iff _ _ _).mpr
    exact ⟨(certificateFamilyValidation U).mpr hU, (t.1, t.2.1),
      Encodable.encodek _, hn, rfl⟩

theorem certificateInvalidInputRejected : Targets.CertificateInvalidInputRejected := by
  intro U hU
  have hf : familyValidTest U ≠ true := fun h => hU ((certificateFamilyValidation U).mp h)
  apply Part.eq_none_iff.mpr
  intro t ht
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec ht
  simpa [atIndex, hf] using hn

end LogicLineages.ModelsAlgebra.Forests.CertificateSearchProof
