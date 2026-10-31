module
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeTargets
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveProof
public import LogicLineages.OrdinalComparison.WWEncodedScalarProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

private theorem normalize_variable (n : Nat) : normalizeScalarSyntaxCode (4*n+1) = 4*n+1 := by
  have hm : (4*n+1)%4=1 := by omega
  rw [normalizeScalarSyntaxCode]
  simp [hm]
private theorem normalize_add (a b : Nat) : normalizeScalarSyntaxCode (4*Nat.pair a b+2) =
    4*Nat.pair (normalizeScalarSyntaxCode a) (normalizeScalarSyntaxCode b)+2 := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [normalizeScalarSyntaxCode]
  simp [hm, hd]
private theorem normalize_shift (h a : Nat) : normalizeScalarSyntaxCode (4*Nat.pair h a+3) =
    4*Nat.pair (encodedClosedHead h) (normalizeScalarSyntaxCode a)+3 := by
  have hm : (4*Nat.pair h a+3)%4=3 := by omega
  have hd : (4*Nat.pair h a+3)/4=Nat.pair h a := by omega
  rw [normalizeScalarSyntaxCode]
  simp [hm, hd]

theorem scalarSyntaxNormalizationCorrect : Targets.ScalarSyntaxNormalizationCorrect := by
  intro ι index s
  induction s with
  | one => simp [scalarSyntaxCode, scalarCode, normalizeScalarSyntaxCode]
  | var x => exact normalize_variable _
  | add a b iha ihb => simp only [scalarSyntaxCode, normalize_add, iha, ihb, scalarCode]
  | shift c a ih =>
    rw [scalarSyntaxCode, normalize_shift, encodedClosedHeadCorrect c, ih]
    rfl

theorem scalarSyntaxNormalizationPrimitiveRecursive : Targets.ScalarSyntaxNormalizationPrimitiveRecursive := by
  let children : Nat → List Nat := fun n => if n%4=0 then [] else if n%4=1 then [] else
    [(n/4).unpair.1, (n/4).unpair.2]
  let assemble : Nat → List Nat → Option Nat := fun n rs => some
    (if n%4=0 then n else if n%4=1 then n
    else if n%4=2 then 4*Nat.pair (rs.getD 0 0) (rs.getD 1 0)+2
    else 4*Nat.pair (encodedClosedHead (n/4).unpair.1) (rs.getD 1 0)+3)
  have hm : Primrec (fun n : Nat => n%4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  have hd : Primrec (fun n : Nat => n/4) := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hc : Primrec children :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const [])
        (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const []))))
  have ha : Primrec₂ assemble := by
    have he (k : Nat) : PrimrecPred (fun p : Nat × List Nat => p.1%4=k) :=
      (Primrec.eq.comp hm (Primrec.const k)).comp Primrec.fst
    have hg (k : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const k)
    have had := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp (hg 0) (hg 1))) (Primrec.const 2)
    have hsh := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp
        (encodedClosedHeadPrimitiveRecursive.comp (hl.comp Primrec.fst)) (hg 1))) (Primrec.const 3)
    exact Primrec.option_some.comp (Primrec.ite (he 0) Primrec.fst
      (Primrec.ite (he 1) Primrec.fst (Primrec.ite (he 2) had hsh)))
  apply Primrec.nat_omega_rec' normalizeScalarSyntaxCode Primrec.id hc ha
  · intro n t ht
    by_cases h0 : n%4=0
    · simp [children, h0] at ht
    by_cases h1 : n%4=1
    · simp [children, h0, h1] at ht
    have hn : 0<n := by omega
    have hdiv := Nat.div_lt_self hn (show 1<4 by decide)
    simp only [children, if_neg h0, if_neg h1, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hdiv
    · exact (Nat.unpair_right_le _).trans_lt hdiv
  · intro n
    rw [normalizeScalarSyntaxCode]
    by_cases h0 : n%4=0
    · simp [children, assemble, h0]
    by_cases h1 : n%4=1
    · simp [children, assemble, h0, h1]
    simp [children, assemble, h0, h1]

theorem scalarSyntaxValueComputable : Targets.ScalarSyntaxValueComputable := by
  have heval : Computable (fun p : Nat × List Nat => encodedScalarValue p.1 p.2) := encodedScalarComputable
  apply (heval.comp ((scalarSyntaxNormalizationPrimitiveRecursive.to_comp.comp Computable.fst).pair Computable.snd)).of_eq
  intro p
  rfl

theorem scalarSyntaxValueSourceCorrect : Targets.ScalarSyntaxValueSourceCorrect := by
  intro ι index s xs
  rw [scalarSyntaxValue, scalarSyntaxNormalizationCorrect ι index s, encodedScalarSourceCorrect ι index s xs]
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
