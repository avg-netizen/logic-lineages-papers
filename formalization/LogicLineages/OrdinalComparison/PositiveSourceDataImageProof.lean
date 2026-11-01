module
public import LogicLineages.OrdinalComparison.PositiveSourceDataSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PositiveSourceDomain

private theorem image_forward (n : Nat) : (encodedPositiveSourceData n).1=1 →
    ∃ E : FixedLimitPositiveExpr, positiveExprEncode E=n ∧ fixedLimitProfileBelow epsilonZero E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hvalid
    have hmod : n%4<4 := Nat.mod_lt _ (by decide)
    have hsum := Nat.mod_add_div n 4
    by_cases h0 : n%4=0
    · refine ⟨.constant (n/4),?_,True.intro⟩
      change 4*(n/4)=n
      omega
    · by_cases h1 : n%4=1
      · by_cases hn : n=1
        · subst n
          exact ⟨.input,rfl,True.intro⟩
        · rw [data_equation] at hvalid
          simp [encodedPositiveSourceDataStep,h0,h1,hn] at hvalid
      · have hn : 0<n := by omega
        have hd : n/4<n := Nat.div_lt_self hn (by decide)
        let p := (n/4).unpair
        have hl : p.1<n := (Nat.unpair_left_le _).trans_lt hd
        have hr : p.2<n := (Nat.unpair_right_le _).trans_lt hd
        have hp : Nat.pair p.1 p.2=n/4 := Nat.pair_unpair _
        by_cases h2 : n%4=2
        · have hchildren : (encodedPositiveSourceData p.1).1=1 ∧
              (encodedPositiveSourceData p.2).1=1 := by
            rw [data_equation] at hvalid
            simp only [encodedPositiveSourceDataStep,if_neg h0,if_neg h1,if_pos h2] at hvalid
            change (if ((encodedPositiveSourceDataTable n).getD p.1 (0,0)).1=1 ∧
              ((encodedPositiveSourceDataTable n).getD p.2 (0,0)).1=1 then (1:Nat) else 0)=1 at hvalid
            rw [table_correct n p.1 hl,table_correct n p.2 hr] at hvalid
            exact (flag_correct _).mp hvalid
          obtain ⟨E,hEcode,hEvalid⟩ := ih p.1 hl hchildren.1
          obtain ⟨F,hFcode,hFvalid⟩ := ih p.2 hr hchildren.2
          refine ⟨.add E F,?_,hEvalid,hFvalid⟩
          rw [positiveExprEncode,hEcode,hFcode,hp]
          omega
        · have h3 : n%4=3 := by omega
          have hhead : encodedPositiveHeadDomain p.1=1 ∧ (encodedPositiveSourceData p.2).1=1 := by
            rw [data_equation] at hvalid
            simp only [encodedPositiveSourceDataStep,if_neg h0,if_neg h1,if_neg h2] at hvalid
            change (if encodedPositiveHeadDomain p.1=1 ∧
              ((encodedPositiveSourceDataTable n).getD p.2 (0,0)).1=1 then (1:Nat) else 0)=1 at hvalid
            rw [table_correct n p.2 hr] at hvalid
            exact (flag_correct _).mp hvalid
          have hNF : ONote.NF (rawNoteDecode p.1) :=
            (rawNormalDecodeCorrect p.1).mp ((head_domain_guard p.1).mp hhead.1).1
          let rho : NONote := ⟨rawNoteDecode p.1,hNF⟩
          have hRcode : rawNoteEncode rho.1=p.1 := by
            simpa only [rho] using rawNoteEncodeDecode p.1
          have hRflag : encodedPositiveHeadDomain (rawNoteEncode rho.1)=1 := by
            rw [hRcode]
            exact hhead.1
          have hRvalid := (head_domain.2 rho).mp hRflag
          obtain ⟨E,hEcode,hEvalid⟩ := ih p.2 hr hhead.2
          refine ⟨.head rho E,?_,hRvalid.1,hRvalid.2,hEvalid⟩
          rw [positiveExprEncode,hRcode,hEcode,hp]
          omega

theorem data_image : Targets.PositiveSourceDataImage := by
  intro n
  constructor
  · exact image_forward n
  · rintro ⟨E,hcode,hvalid⟩
    rw [← hcode]
    exact (data_program.2 E).1.mpr hvalid

end LogicLineages.OrdinalComparison.PositiveSourceDomain
