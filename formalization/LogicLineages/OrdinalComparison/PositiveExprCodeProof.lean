module
public import LogicLineages.OrdinalComparison.PositiveExprCodeTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem expr_decode_const (n : Nat) : positiveExprDecode (4*n)=some (.constant n) := by
  have hm : (4*n)%4=0 := by omega
  have hd : (4*n)/4=n := by omega
  rw [positiveExprDecode]
  simp [hm,hd]

private theorem expr_decode_input : positiveExprDecode 1=some .input := by
  rw [positiveExprDecode]
  norm_num

private theorem expr_decode_bad_input (n : Nat) (hn : 0<n) : positiveExprDecode (4*n+1)=none := by
  have hm : (4*n+1)%4=1 := by omega
  have hne : 4*n+1≠1 := by omega
  rw [positiveExprDecode]
  simp [hm, Nat.ne_of_gt hn]

private theorem expr_decode_add (a b : Nat) :
    positiveExprDecode (4*Nat.pair a b+2)=
      (positiveExprDecode a).bind (fun E => (positiveExprDecode b).map (fun F => .add E F)) := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [positiveExprDecode]
  simp only [hm,hd,Nat.unpair_pair]
  norm_num

private theorem expr_decode_head (h a : Nat) :
    positiveExprDecode (4*Nat.pair h a+3)=
      if hh : rawNormalCode h=1 then
        (positiveExprDecode a).map (fun E => .head ⟨rawNoteDecode h,(rawNormalDecodeCorrect h).mp hh⟩ E)
      else none := by
  have hm : (4*Nat.pair h a+3)%4=3 := by omega
  have hd : (4*Nat.pair h a+3)/4=Nat.pair h a := by omega
  rw [positiveExprDecode]
  simp only [hm,hd,Nat.unpair_pair]
  norm_num

theorem positiveExprCodeRoundTrip : Targets.PositiveExprCodeRoundTrip := by
  intro E
  induction E with
  | constant n => exact expr_decode_const n
  | input => exact expr_decode_input
  | add E F ihE ihF =>
    rw [positiveExprEncode,expr_decode_add,ihE,ihF]
    rfl
  | head rho E ih =>
    have hn : rawNormalCode (rawNoteEncode rho.1)=1 := (rawNormalCorrect rho.1).mpr rho.2
    rw [positiveExprEncode,expr_decode_head,dif_pos hn,ih]
    have heq : (⟨rawNoteDecode (rawNoteEncode rho.1),
        (rawNormalDecodeCorrect (rawNoteEncode rho.1)).mp hn⟩ : NONote)=rho := by
      apply Subtype.ext
      exact rawNoteDecodeEncode rho.1
    simp only [Option.map_some,heq]

theorem positiveExprCodeInverse : Targets.PositiveExprCodeInverse := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E hdec
    have hm : n%4<4 := Nat.mod_lt _ (by decide)
    have hdiv := Nat.mod_add_div n 4
    by_cases h0 : n%4=0
    · have heq : n=4*(n/4) := by omega
      rw [heq,expr_decode_const] at hdec
      have hE : FixedLimitPositiveExpr.constant (n/4)=E := Option.some.inj hdec
      subst E
      exact heq.symm
    · by_cases h1 : n%4=1
      · by_cases hn : n=1
        · subst n
          rw [expr_decode_input] at hdec
          have hE : FixedLimitPositiveExpr.input=E := Option.some.inj hdec
          subst E
          rfl
        · have hp : 0<n/4 := by omega
          have heq : n=4*(n/4)+1 := by omega
          rw [heq,expr_decode_bad_input _ hp] at hdec
          cases hdec
      · have hn : 0<n := by omega
        have hd : n/4<n := Nat.div_lt_self hn (by decide)
        let p := (n/4).unpair
        have hleft : p.1<n := (Nat.unpair_left_le _).trans_lt hd
        have hright : p.2<n := (Nat.unpair_right_le _).trans_lt hd
        have hp : Nat.pair p.1 p.2=n/4 := Nat.pair_unpair _
        by_cases h2 : n%4=2
        · have heq : n=4*Nat.pair p.1 p.2+2 := by rw [hp]; omega
          rw [heq,expr_decode_add] at hdec
          cases ha : positiveExprDecode p.1 with
          | none => simp [ha] at hdec
          | some A =>
            cases hb : positiveExprDecode p.2 with
            | none => simp [ha,hb] at hdec
            | some B =>
              have hE : FixedLimitPositiveExpr.add A B=E := by
                apply Option.some.inj
                simpa only [ha,hb,Option.bind_some,Option.map_some] using hdec
              subst E
              rw [positiveExprEncode,ih p.1 hleft A ha,ih p.2 hright B hb]
              exact heq.symm
        · have h3 : n%4=3 := by omega
          have heq : n=4*Nat.pair p.1 p.2+3 := by rw [hp]; omega
          rw [heq,expr_decode_head] at hdec
          by_cases hh : rawNormalCode p.1=1
          · rw [dif_pos hh] at hdec
            cases ha : positiveExprDecode p.2 with
            | none => simp [ha] at hdec
            | some A =>
              let rho : NONote := ⟨rawNoteDecode p.1,(rawNormalDecodeCorrect p.1).mp hh⟩
              have hE : FixedLimitPositiveExpr.head rho A=E := by
                apply Option.some.inj
                simpa only [ha,Option.map_some] using hdec
              subst E
              rw [positiveExprEncode,ih p.2 hright A ha]
              change 4*Nat.pair (rawNoteEncode (rawNoteDecode p.1)) p.2+3=n
              rw [rawNoteEncodeDecode]
              exact heq.symm
          · rw [dif_neg hh] at hdec
            cases hdec

theorem positiveExprCodeDomain : Targets.PositiveExprCodeDomain := by
  intro n
  constructor
  · intro h
    cases hd : positiveExprDecode n with
    | none => simp [hd] at h
    | some E => exact ⟨E,positiveExprCodeInverse n E hd⟩
  · rintro ⟨E,rfl⟩
    rw [positiveExprCodeRoundTrip E]
    rfl

theorem positiveExprMalformedRejected : Targets.PositiveExprMalformedRejected := by
  refine ⟨expr_decode_bad_input,?_⟩
  intro h a hh
  rw [expr_decode_head,dif_neg hh]

end LogicLineages.OrdinalComparison
