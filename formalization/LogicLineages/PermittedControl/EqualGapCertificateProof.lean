module
public import LogicLineages.PermittedControl.EqualGapCertificateCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem actualEqualGapCertificate : Targets.ActualEqualGapCertificate := by
  intro f B hf mu nu delta A A' t hmud hnud hdl hA hA' ht hp hp' hn hn'
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hd := normalRepresentationSound delta
  let E := Ordinal.log Ordinal.omega0 delta.1.repr
  let ec := originalLeadingCode (rawNoteEncode delta.1)
  have hlead := original_leading_code_correct delta hdl.bot_lt.ne'
  change ONote.NF (rawNoteDecode ec) ∧ (rawNoteDecode ec).repr=E at hlead
  let en : NONote := ⟨rawNoteDecode ec,hlead.1⟩
  have hen : rawNoteEncode en.1=ec := rawNoteEncodeDecode ec
  have hEn : en.1.repr=E := hlead.2
  have hEp : 0 < E := Ordinal.log_pos Ordinal.one_lt_omega0 hdl.bot_lt.ne' (Ordinal.omega0_le_of_isSuccLimit hdl)
  have hE1 : 1 ≤ E := Order.one_le_iff_pos.mpr hEp
  have hPw : Ordinal.omega0 ≤ Ordinal.omega0^E := Ordinal.left_le_opow _ hEp
  have hitail := equalGap_tail_initial mu nu delta B t ht
  have hR := initial_radius_bounds mu.1.repr nu.1.repr delta.1.repr
  have hlarge := sensitive_tail_large _ B t hitail
  have hmuN : actualOrdinalNorm mu.1.repr ≤ t := by omega
  have hnuN : actualOrdinalNorm nu.1.repr ≤ t := by omega
  have hmuA : mu.1.repr ≤ A := (le_self_add : mu.1.repr ≤ mu.1.repr+delta.1.repr).trans
    (by rw [←hp]; exact Ordinal.mul_div_le _ _)
  have hnuA : nu.1.repr ≤ A' := (le_self_add : nu.1.repr ≤ nu.1.repr+delta.1.repr).trans
    (by rw [←hp']; exact Ordinal.mul_div_le _ _)
  obtain ⟨tau,hHit,hNt⟩ := entry_exists_state f (selected_threshold_admissible f B hf).2 mu.1.repr hmud A hA hmuA (by omega)
  obtain ⟨sigma,hHit',hNs⟩ := entry_exists_state f (selected_threshold_admissible f B hf).2 nu.1.repr hnud A' hA' hnuA (by omega)
  refine ⟨tau,sigma,hHit,hHit',by simpa only [hn] using hNt,by simpa only [hn'] using hNs,?_⟩
  have hinit := actualInitialPeeling f B hf mu.1.repr nu.1.repr delta.1.repr A A' t
    hmu hnu hd hA hA' hmud hnud hdl hitail hp hp' hn hn'
  by_cases hpass : initialPassCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode delta.1)=true
  · have hsemantic := (initialPassCodeCorrect mu nu delta hdl).mp hpass
    obtain ⟨i,hi,hi',hiN,hiN'⟩ := hinit.1 hsemantic
    have hhead := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hEp.ne'
    have hlim := (interval_iff_limitPart _ (mu.1.repr+Ordinal.omega0^E) (Or.inr (Ordinal.isSuccLimit_add mu.1.repr hhead))).mp ⟨hi.1,hi.2.1⟩
    have hlim' := (interval_iff_limitPart _ (nu.1.repr+Ordinal.omega0^E) (Or.inr (Ordinal.isSuccLimit_add nu.1.repr hhead))).mp ⟨hi'.1,hi'.2.1⟩
    have htail : pureCertificateTailCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode en.1) B ≤ f^[i] t := by
      rw [hen]
      exact ((le_max_right _ _).trans ht).trans (iterate_self_le (control_self_le f (selected_threshold_admissible f B hf).2) i t)
    obtain ⟨p,q,hpHit,hqHit,_,_,hcomp⟩ := actualPureCertificate f B hf mu nu en _ _ (f^[i] t)
      hmud hnud (by rwa [hEn]) (trajectory_below f A hA i) (trajectory_below f A' hA' i) htail
      (by rwa [hEn]) (by rwa [hEn]) hiN hiN'
    have hfull := compose_pure_entry f mu.1.repr E A i p hA hE1 hi hpHit
    have hfull' := compose_pure_entry f nu.1.repr E A' i q hA' hE1 hi' hqHit
    have he := firstEntry_unique f A mu.1.repr (i+p) tau hfull hHit
    have he' := firstEntry_unique f A' nu.1.repr (i+q) sigma hfull' hHit'
    rw [equalGapCertificateCode,if_pos hpass,←he,←he']
    rw [hen] at hcomp
    simpa only [entryNormAt,Nat.add_comm i p,Nat.add_comm i q,Function.iterate_add_apply] using hcomp
  · have hsemantic : ¬ initialPeelingPass mu.1.repr nu.1.repr delta.1.repr := fun h => hpass ((initialPassCodeCorrect mu nu delta hdl).mpr h)
    obtain ⟨i,hne,hsign,hkeep,hkeep'⟩ := hinit.2 hsemantic
    have hraw := initial_leading_data mu nu delta hdl
    have hc : compare (entryNormAt f A tau) (entryNormAt f A' sigma)=
      compare (relativeProfile nu.1.repr E) (relativeProfile mu.1.repr E) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have ho := entry_order_from_oriented f B hf nu.1.repr mu.1.repr _ A' A t sigma tau hnu hmu hA' hA hnud hmud hPw
          hn' hn hnuN hmuN hHit' hHit ⟨i,hlt,hkeep,hkeep'⟩
        exact (compare_lt_iff_lt.mpr ho).trans ((compare_lt_iff_lt.mpr hlt).symm.trans hsign)
      · have ho := entry_order_from_oriented f B hf mu.1.repr nu.1.repr _ A A' t tau sigma hmu hnu hA hA' hmud hnud hPw
          hn hn' hmuN hnuN hHit hHit' ⟨i,hgt,hkeep',hkeep⟩
        exact (compare_gt_iff_gt.mpr ho).trans ((compare_gt_iff_gt.mpr hgt).symm.trans hsign)
    rw [equalGapCertificateCode,if_neg hpass,hraw.1,hraw.2.1]
    exact numericalComparison_compare _ _ _ _ hc

end LogicLineages.PermittedControl
