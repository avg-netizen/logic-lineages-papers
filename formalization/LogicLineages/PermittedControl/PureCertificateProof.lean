module
public import LogicLineages.PermittedControl.PureCertificateLimitProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualPureCertificate : Targets.ActualPureCertificate := by
  intro f B hf mu nu E A A' t hmud hnud hE1 hA hA' ht hp hp' hn hn'
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hE := normalRepresentationSound E
  let R := 100+4*(actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr+actualOrdinalNorm E.1.repr)
  have hmN := (rawNormCodeCorrect mu.1).trans (actualOrdinalNorm_notationCorrespondence mu).symm
  have hnN := (rawNormCodeCorrect nu.1).trans (actualOrdinalNorm_notationCorrespondence nu).symm
  have heN := (rawNormCodeCorrect E.1).trans (actualOrdinalNorm_notationCorrespondence E).symm
  have htail : thickBlockTail R B ≤ t := by
    simpa only [pureCertificateTailCode,pureCertificateRadiusCode,hmN,hnN,heN,R] using ht
  have hR : 20 ≤ R := by dsimp only [R]; omega
  have hmuR : actualOrdinalNorm mu.1.repr ≤ R := by dsimp only [R]; omega
  have hnuR : actualOrdinalNorm nu.1.repr ≤ R := by dsimp only [R]; omega
  have hER : actualOrdinalNorm E.1.repr ≤ R := by dsimp only [R]; omega
  have hlarge := sensitive_tail_large R B t htail
  have hmuA : mu.1.repr ≤ A := (le_self_add : mu.1.repr ≤ mu.1.repr+Ordinal.omega0^E.1.repr).trans
    (by rw [←hp]; exact Ordinal.mul_div_le _ _)
  have hnuA : nu.1.repr ≤ A' := (le_self_add : nu.1.repr ≤ nu.1.repr+Ordinal.omega0^E.1.repr).trans
    (by rw [←hp']; exact Ordinal.mul_div_le _ _)
  obtain ⟨tau,hHit,hNt⟩ := entry_exists_state f (selected_threshold_admissible f B hf).2 mu.1.repr hmud A hA hmuA (by omega)
  obtain ⟨sigma,hHit',hNs⟩ := entry_exists_state f (selected_threshold_admissible f B hf).2 nu.1.repr hnud A' hA' hnuA (by omega)
  refine ⟨tau,sigma,hHit,hHit',by simpa only [hn] using hNt,by simpa only [hn'] using hNs,?_⟩
  have hrawE : rawComparisonCode (rawNoteEncode E.1) (rawNoteEncode (ONote.ofNat 1))=1 ↔ E.1.repr=1 := by
    have h := (rawComparisonOrdinalCorrect E (NONote.ofNat 1)).2.1
    change rawComparisonCode (rawNoteEncode E.1) (rawNoteEncode (ONote.ofNat 1))=1 ↔ E.1.repr=(ONote.ofNat 1).repr at h
    simpa using h
  by_cases heq : E.1.repr=1
  · have he := actualTerminalOmega f B hf mu.1.repr A t hmu hA hmud (by simpa only [heq,Ordinal.opow_one] using hp) hn
    have he' := actualTerminalOmega f B hf nu.1.repr A' t hnu hA' hnud (by simpa only [heq,Ordinal.opow_one] using hp') hn'
    have hte := firstEntry_unique f A mu.1.repr tau 1 hHit he.1
    have hse := firstEntry_unique f A' nu.1.repr sigma 1 hHit' he'.1
    rw [hte,hse,he.2,he'.2]
    simp only [pureCertificateCode,hrawE.mpr heq,↓reduceIte,numericalComparison,lt_self_iff_false,ite_false,ite_true]
  · have hE2 : (2 : Ordinal) ≤ E.1.repr := by
      have hh : (1 : Ordinal) < E.1.repr := lt_of_le_of_ne hE1 (Ne.symm heq)
      simpa only [one_add_one_eq_two] using Order.add_one_le_iff.mpr hh
    have hrawne : rawComparisonCode (rawNoteEncode E.1) (rawNoteEncode (ONote.ofNat 1)) ≠ 1 := fun h => heq (hrawE.mp h)
    unfold pureCertificateCode
    rw [if_neg hrawne]
    cases hsel : highestPieceCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1) with
    | none =>
      have hagree := (highestPieceNone mu nu E).mp hsel
      have hc := pure_terminal_comparison f B hf mu.1.repr nu.1.repr E.1.repr A A' R t tau sigma
        hmu hnu hE hA hA' hmud hnud hE2 hR hmuR hnuR hER htail hp hp' hn hn' hagree hHit hHit'
      have hp1 : rawProfileCode (rawNoteEncode mu.1) (rawNoteEncode (ONote.ofNat 1))=relativeProfile mu.1.repr 1 := by
        have h := rawProfileCorrect mu (NONote.ofNat 1)
        change rawProfileCode (rawNoteEncode mu.1) (rawNoteEncode (ONote.ofNat 1))=relativeProfile mu.1.repr (ONote.ofNat 1).repr at h
        simpa using h
      have hp1' : rawProfileCode (rawNoteEncode nu.1) (rawNoteEncode (ONote.ofNat 1))=relativeProfile nu.1.repr 1 := by
        have h := rawProfileCorrect nu (NONote.ofNat 1)
        change rawProfileCode (rawNoteEncode nu.1) (rawNoteEncode (ONote.ofNat 1))=relativeProfile nu.1.repr (ONote.ofNat 1).repr at h
        simpa using h
      rw [hp1,hp1']
      exact numericalComparison_compare _ _ _ _ hc
    | some n =>
      rcases highestPhaseGeometry mu nu E n hsel with hs | hl
      · obtain ⟨beta,hb2,hbE,hb,hbN,_,hdiff,hagree,hsign⟩ := hs
        have hbsN : actualOrdinalNorm (beta+1)=actualOrdinalNorm beta+1 := by
          simpa only [Nat.cast_one] using (actualFiniteTailClosureNorm beta hb 1).2
        have hbR : actualOrdinalNorm beta ≤ R := by dsimp only [R] at *; omega
        have hbsR : actualOrdinalNorm (beta+1) ≤ R := by dsimp only [R] at *; omega
        have hc := pure_successor_comparison f B hf mu.1.repr nu.1.repr E.1.repr beta A A' R t tau sigma
          hmu hnu hE hb hA hA' hmud hnud hb2 hbE hR hmuR hnuR hER hbR hbsR htail hp hp' hn hn' hagree hdiff hHit hHit'
        exact numericalComparison_compare _ _ _ _ (hc.trans hsign)
      · obtain ⟨hEl,zeta,hz2,hzE,hz,hzN,_,hdiff,hconst,hsign⟩ := hl
        have hzR : actualOrdinalNorm zeta ≤ R := by dsimp only [R] at *; omega
        have hc := pure_limit_comparison f B hf mu.1.repr nu.1.repr E.1.repr zeta A A' R t tau sigma
          hmu hnu hE hz hA hA' hmud hnud hEl hz2 hzE hR hmuR hnuR hER hzR htail hp hp' hn hn'
          (fun e he heE => (hconst e he heE).1) (fun e he heE => (hconst e he heE).2) hdiff hHit hHit'
        exact numericalComparison_compare _ _ _ _ (hc.trans hsign)

 theorem pureCertificateFoundation : Targets.PureCertificateFoundation := ⟨pureCertificateEffective,actualPureCertificate⟩
end LogicLineages.PermittedControl
