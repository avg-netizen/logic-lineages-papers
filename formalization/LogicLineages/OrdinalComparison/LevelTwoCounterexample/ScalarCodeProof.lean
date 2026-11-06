module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarTargets
import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof
import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionProgramStatementChecks

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarCodeProof
open Source Source.ForwardTranslation PolynomialGraphCompletion

private theorem lower_numeral (n : Nat) : ScalarCode.lower (4*n) = 5*n := by
  rw [ScalarCode.lower]
  simp

private theorem lower_variable (n : Nat) : ScalarCode.lower (4*n+1) = 5*n+1 := by
  have hm : (4*n+1)%4=1 := by omega
  have hd : (4*n+1)/4=n := by omega
  rw [ScalarCode.lower]
  simp [hm,hd]

private theorem lower_add (a b : Nat) : ScalarCode.lower (4*Nat.pair a b+2) =
    5*Nat.pair (ScalarCode.lower a) (ScalarCode.lower b)+2 := by
  have hm : (4*Nat.pair a b+2)%4=2 := by omega
  have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
  rw [ScalarCode.lower]
  simp [hm,hd]

private theorem lower_shift (h a : Nat) : ScalarCode.lower (4*Nat.pair h a+3) =
    5*Nat.pair h (ScalarCode.lower a)+4 := by
  have hm : (4*Nat.pair h a+3)%4=3 := by omega
  have hd : (4*Nat.pair h a+3)/4=Nat.pair h a := by omega
  rw [ScalarCode.lower]
  simp [hm,hd]

private theorem literal_normalized (ι : Type) (index : ι → Nat) (s : Scalar ι) :
    ScalarCode.lower (scalarCode index s) = (scalarExpr index s).encode := by
  induction s with
  | one => exact lower_numeral 1
  | var x => exact lower_variable (index x)
  | add a b iha ihb => simp only [scalarCode, scalarExpr, Expr.encode, lower_add, iha, ihb]
  | shift c a ih => simp only [scalarCode, scalarExpr, Expr.encode, lower_shift, ih]

theorem literalScalarCode : ScalarTargets.LiteralScalarCode := by
  intro ι index s
  refine ⟨literal_normalized ι index s, ?_⟩
  rw [ScalarCode.lowerSyntax, scalarSyntaxNormalizationCorrect]
  exact literal_normalized ι index s

theorem literalGraphPackage : ScalarTargets.LiteralGraphPackage := by
  intro ι index s resultName
  rw [ScalarCode.package, (literalScalarCode ι index s).2]
  exact ExpressionProgramStatementChecks.literal_graph_compiler _ _

theorem lower_primitive : Primrec ScalarCode.lower := by
  let children : Nat → List Nat := fun n =>
    if n % 4 = 0 then [] else if n % 4 = 1 then [] else
      if n % 4 = 2 then [(n/4).unpair.1,(n/4).unpair.2] else [(n/4).unpair.2]
  let assemble : Nat → List Nat → Option Nat := fun n rs => some
    (if n % 4 = 0 then 5*(n/4) else if n % 4 = 1 then 5*(n/4)+1
      else if n % 4 = 2 then 5*Nat.pair (rs.getD 0 0) (rs.getD 1 0)+2
      else 5*Nat.pair (n/4).unpair.1 (rs.getD 0 0)+4)
  have hm : Primrec (fun n : Nat => n % 4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  have hd : Primrec (fun n : Nat => n / 4) := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have he (k : Nat) : PrimrecPred (fun n : Nat => n % 4 = k) := Primrec.eq.comp hm (Primrec.const k)
  have hc : Primrec children :=
    Primrec.ite (he 0) (Primrec.const [])
      (Primrec.ite (he 1) (Primrec.const [])
        (Primrec.ite (he 2)
          (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const [])))
          (Primrec.list_cons.comp hr (Primrec.const []))))
  have ha : Primrec₂ assemble := by
    have hget (k : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const k)
    have hmul : Primrec (fun p : Nat × List Nat => 5*(p.1/4)) :=
      Primrec.nat_mul.comp (Primrec.const 5) (hd.comp Primrec.fst)
    apply Primrec.option_some.comp
    exact Primrec.ite ((he 0).comp Primrec.fst) hmul
      (Primrec.ite ((he 1).comp Primrec.fst)
        (Primrec.nat_add.comp hmul (Primrec.const 1))
        (Primrec.ite ((he 2).comp Primrec.fst)
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 5) (Primrec₂.natPair.comp (hget 0) (hget 1)))
            (Primrec.const 2))
          (Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.const 5)
              (Primrec₂.natPair.comp (hl.comp Primrec.fst) (hget 0))) (Primrec.const 4))))
  apply Primrec.nat_omega_rec' ScalarCode.lower Primrec.id hc ha
  · intro n t ht
    by_cases h0 : n%4=0
    · simp [children,h0] at ht
    by_cases h1 : n%4=1
    · simp [children,h0,h1] at ht
    have hn : 0<n := by omega
    have hdlt := Nat.div_lt_self hn (show 1<4 by decide)
    by_cases h2 : n%4=2
    · simp only [children,if_neg h0,if_neg h1,if_pos h2,List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact (Nat.unpair_left_le _).trans_lt hdlt
      · exact (Nat.unpair_right_le _).trans_lt hdlt
    · simp only [children,if_neg h0,if_neg h1,if_neg h2,List.mem_singleton] at ht
      subst t
      exact (Nat.unpair_right_le _).trans_lt hdlt
  · intro n
    rw [ScalarCode.lower]
    by_cases h0 : n%4=0
    · simp [children,assemble,h0]
    by_cases h1 : n%4=1
    · simp [children,assemble,h0,h1]
    by_cases h2 : n%4=2 <;> simp [children,assemble,h0,h1,h2]

theorem actualNumericPrograms : ScalarTargets.ActualNumericPrograms := by
  have hs : Primrec ScalarCode.lowerSyntax := lower_primitive.comp scalarSyntaxNormalizationPrimitiveRecursive
  refine ⟨lower_primitive, hs, ?_⟩
  exact ExpressionProgramStatementChecks.actual_numeric_program.2.2.comp
    (hs.comp Primrec.fst) Primrec.snd
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarCodeProof
