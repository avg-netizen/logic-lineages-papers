module
public import LogicLineages.PermittedControl.InitialExceptionEquivalenceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem initialPassCode_boolean (mu nu delta : Nat) :
    initialPassCode mu nu delta=true ↔
    (rawProfileCode mu (originalLeadingCode delta)=rawProfileCode nu (originalLeadingCode delta) ∨
      (originalUnitCodes delta).tail.all (fun e => decide (rawComparisonCode e (rawNoteEncode (ONote.ofNat 2))=0))=true) ∨
    ((rawProfileCode mu (originalLeadingCode delta)=rawProfileCode nu (originalLeadingCode delta)+1 ∨
      rawProfileCode nu (originalLeadingCode delta)=rawProfileCode mu (originalLeadingCode delta)+1) ∧
     ((rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) (originalLeadingCode delta) ≠ 2 ∧
        originalQuadraticRemainder (originalUnitCodes delta).tail=true) ∨
      (originalLeadingCode delta=rawNoteEncode (ONote.ofNat 2) ∧
        originalQuadraticRemainder (originalUnitCodes delta).tail=true)) ∧
      (min (rawProfileCode mu (originalLeadingCode delta)) (rawProfileCode nu (originalLeadingCode delta))+
        (1+rawNormCode (originalLeadingCode delta)))%2=1) := by
  simp only [initialPassCode,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc]

 theorem initial_leading_data (mu nu delta : NONote) (hlim : Order.IsSuccLimit delta.1.repr) :
    let ec := originalLeadingCode (rawNoteEncode delta.1)
    let E := Ordinal.log Ordinal.omega0 delta.1.repr
    rawProfileCode (rawNoteEncode mu.1) ec=relativeProfile mu.1.repr E ∧
    rawProfileCode (rawNoteEncode nu.1) ec=relativeProfile nu.1.repr E ∧
    1+rawNormCode ec=actualOrdinalNorm (Ordinal.omega0^E) ∧
    (rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) ec ≠ 2 ↔ (3 : Ordinal) ≤ E) ∧
    (ec=rawNoteEncode (ONote.ofNat 2) ↔ E=2) := by
  let dc := rawNoteEncode delta.1
  let ec := originalLeadingCode dc
  let E := Ordinal.log Ordinal.omega0 delta.1.repr
  let l := originalUnitCodes dc
  have hd := normalRepresentationSound delta
  have hp := hlim.bot_lt.ne'
  have hlead := original_leading_code_correct delta hp
  change ONote.NF (rawNoteDecode ec) ∧ (rawNoteDecode ec).repr=E at hlead
  let en : NONote := ⟨rawNoteDecode ec,hlead.1⟩
  have hm : rawProfileCode (rawNoteEncode mu.1) ec=relativeProfile mu.1.repr E := by
    have h := rawProfileCorrect mu en
    change rawProfileCode (rawNoteEncode mu.1) (rawNoteEncode (rawNoteDecode ec))=relativeProfile mu.1.repr (rawNoteDecode ec).repr at h
    rwa [rawNoteEncodeDecode,hlead.2] at h
  have hn : rawProfileCode (rawNoteEncode nu.1) ec=relativeProfile nu.1.repr E := by
    have h := rawProfileCorrect nu en
    change rawProfileCode (rawNoteEncode nu.1) (rawNoteEncode (rawNoteDecode ec))=relativeProfile nu.1.repr (rawNoteDecode ec).repr at h
    rwa [rawNoteEncodeDecode,hlead.2] at h
  have hnorm : 1+rawNormCode ec=actualOrdinalNorm (Ordinal.omega0^E) := by
    have h := (rawNormCodeCorrect (rawNoteDecode ec)).trans (actualOrdinalNorm_notationCorrespondence en).symm
    rw [rawNoteEncodeDecode] at h
    change rawNormCode ec=actualOrdinalNorm (rawNoteDecode ec).repr at h
    rw [hlead.2] at h
    have hE := (initial_leading_norm delta.1.repr hd hp).1
    have hpow := thick_monomial_norm E hE 1
    simpa only [Nat.cast_one,mul_one,one_mul,h] using hpow.symm
  have hge : rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) ec ≠ 2 ↔ (3 : Ordinal) ≤ E := by
    simpa only [hlead.2] using normal_code_ge_three ec hlead.1
  have heq : ec=rawNoteEncode (ONote.ofNat 2) ↔ E=2 := by
    simpa only [hlead.2,Nat.cast_ofNat] using normal_code_finite_eq ec 2 hlead.1
  exact ⟨hm,hn,hnorm,hge,heq⟩

 theorem initial_tail_data (delta : NONote) :
    let l := originalUnitCodes (rawNoteEncode delta.1)
    (l.tail.all (fun c => decide (rawComparisonCode c (rawNoteEncode (ONote.ofNat 2))=0))=true ↔
      ∀ a ∈ initialPeelingUnits delta.1.repr, a < 2) ∧
    (originalQuadraticRemainder l.tail=true ↔ ∃ n : Nat,
      (originalGapUnits delta.1.repr).tail=(2 : Ordinal)::List.replicate n 1) := by
  let l := originalUnitCodes (rawNoteEncode delta.1)
  have hcodes := originalUnitCodeCorrect delta
  have htail : l.tail.map (fun c => (rawNoteDecode c).repr)=(originalGapUnits delta.1.repr).tail := by
    have h := congrArg List.tail hcodes.1
    simpa only [List.map_tail] using h
  have hnormal : ∀ c ∈ l.tail, ONote.NF (rawNoteDecode c) := by
    intro c hc
    exact hcodes.2 c (List.mem_of_mem_tail hc)
  have hsmall : l.tail.all (fun c => decide (rawComparisonCode c (rawNoteEncode (ONote.ofNat 2))=0))=true ↔
      ∀ a ∈ initialPeelingUnits delta.1.repr, a < 2 := by
    rw [List.all_eq_true]
    constructor
    · intro h a ha
      have ha' : a ∈ l.tail.map (fun c => (rawNoteDecode c).repr) := by
        rw [htail]
        simpa only [initialPeelingUnits,List.mem_reverse] using ha
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha'
      exact (normal_code_lt_two c (hnormal c hc)).mp (of_decide_eq_true (h c hc))
    · intro h c hc
      apply decide_eq_true
      apply (normal_code_lt_two c (hnormal c hc)).mpr
      apply h
      have hh : (rawNoteDecode c).repr ∈ (originalGapUnits delta.1.repr).tail := by
        rw [←htail]
        exact List.mem_map.mpr ⟨c,hc,rfl⟩
      simpa only [initialPeelingUnits,List.mem_reverse] using hh
  have hquad : originalQuadraticRemainder l.tail=true ↔ ∃ n : Nat,
      (originalGapUnits delta.1.repr).tail=(2 : Ordinal)::List.replicate n 1 := by
    simpa only [htail] using quadratic_remainder_actual l.tail hnormal
  exact ⟨hsmall,hquad⟩

attribute [local irreducible] rawProfileCode rawNormCode rawComparisonCode originalUnitCodes originalLeadingCode originalQuadraticRemainder

 theorem initialPassCodeCorrect : Targets.InitialPassCodeCorrect := by
  intro mu nu delta hlim
  let dc := rawNoteEncode delta.1
  let ec := originalLeadingCode dc
  let E := Ordinal.log Ordinal.omega0 delta.1.repr
  let l := originalUnitCodes dc
  have hd := normalRepresentationSound delta
  have hp := hlim.bot_lt.ne'
  trace "BEFORE obtain ⟨hm"
  obtain ⟨hm,hn,hnorm,hge,heq⟩ := initial_leading_data mu nu delta hlim
  trace "BEFORE obtain ⟨hsmall"
  obtain ⟨hsmall,hquad⟩ := initial_tail_data delta
  trace "BEFORE have hex"
  have hex := initial_exception_list_iff delta.1.repr hd hp (relativeProfile mu.1.repr E) (relativeProfile nu.1.repr E)
  trace "BEFORE rw [initialPassCode_boolean]"
  rw [initialPassCode_boolean]
  trace "BEFORE change (rawProfileCode"
  change (rawProfileCode (rawNoteEncode mu.1) ec=rawProfileCode (rawNoteEncode nu.1) ec ∨
    l.tail.all (fun e => decide (rawComparisonCode e (rawNoteEncode (ONote.ofNat 2))=0))=true) ∨
    ((rawProfileCode (rawNoteEncode mu.1) ec=rawProfileCode (rawNoteEncode nu.1) ec+1 ∨
      rawProfileCode (rawNoteEncode nu.1) ec=rawProfileCode (rawNoteEncode mu.1) ec+1) ∧
     ((rawComparisonCode (rawNoteEncode (ONote.ofNat 3)) ec ≠ 2 ∧ originalQuadraticRemainder l.tail=true) ∨
      (ec=rawNoteEncode (ONote.ofNat 2) ∧ originalQuadraticRemainder l.tail=true)) ∧
      (min (rawProfileCode (rawNoteEncode mu.1) ec) (rawProfileCode (rawNoteEncode nu.1) ec)+(1+rawNormCode ec))%2=1) ↔ _
  trace "BEFORE rw [hm,hn"
  rw [hm,hn,hsmall,hquad,hge,heq,hnorm]
  trace "BEFORE unfold initialPeelingPass"
  unfold initialPeelingPass
  trace "BEFORE change _ ↔ relativeProfile"
  change _ ↔ relativeProfile mu.1.repr E=relativeProfile nu.1.repr E ∨
    (∀ a ∈ initialPeelingUnits delta.1.repr, a < 2) ∨ _
  trace "BEFORE clear * - hex"
  clear * - hex
  trace "BEFORE tauto"
  tauto

 theorem initialCodeFoundation : Targets.InitialCodeFoundation :=
  ⟨initialCodeEffective,originalUnitCodeCorrect,initialPassCodeCorrect⟩
end LogicLineages.PermittedControl
