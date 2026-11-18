module
public import LogicLineages.StandardControlCurrent.PolicyFiniteSemanticProof
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation

theorem checker_primitive : Primrec PolicyFinite.finiteScalarCode := by
  let children : Nat → List Nat := fun n => if n%4=0 then [] else if n%4=1 then [] else
    [(n/4).unpair.1,(n/4).unpair.2]
  let assemble : Nat → List Bool → Option Bool := fun n rs => some
    (if n%4=0 then true else if n%4=1 then true else if n%4=2 then rs.getD 0 true && rs.getD 1 true
    else decide (rawComparisonCode (encodedClosedPositive (n/4).unpair.1)
      (rawNoteEncode (.oadd 1 1 .zero))=0) && rs.getD 1 true)
  have hm : Primrec (fun n : Nat => n%4) := Primrec.nat_mod.comp Primrec.id (Primrec.const 4)
  have hd : Primrec (fun n : Nat => n/4) := Primrec.nat_div.comp Primrec.id (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hc : Primrec children :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const [])
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1)) (Primrec.const [])
        (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const []))))
  have ha : Primrec₂ assemble := by
    have he (k : Nat) : PrimrecPred (fun p : Nat × List Bool => p.1%4=k) :=
      (Primrec.eq.comp hm (Primrec.const k)).comp Primrec.fst
    have hg (k : Nat) : Primrec (fun p : Nat × List Bool => p.2.getD k true) :=
      (Primrec.list_getD true).comp Primrec.snd (Primrec.const k)
    have hcmp : Primrec (fun p : Nat × List Bool => rawComparisonCode
        (encodedClosedPositive (p.1/4).unpair.1) (rawNoteEncode (.oadd 1 1 .zero))) := rawComparisonPrimitiveRecursive.comp
      (encodedClosedPositivePrimitiveRecursive.comp (hl.comp Primrec.fst))
      (Primrec.const (rawNoteEncode (.oadd 1 1 .zero)))
    have hflag := (Primrec.eq.comp hcmp (Primrec.const 0)).decide
    exact Primrec.option_some.comp (Primrec.ite (he 0) (Primrec.const true)
      (Primrec.ite (he 1) (Primrec.const true)
        (Primrec.ite (he 2) (Primrec.and.comp (hg 0) (hg 1)) (Primrec.and.comp hflag (hg 1)))))
  apply Primrec.nat_omega_rec' PolicyFinite.finiteScalarCode Primrec.id hc ha
  · intro n t ht
    by_cases h0 : n%4=0
    · simp [children,h0] at ht
    by_cases h1 : n%4=1
    · simp [children,h0,h1] at ht
    have hn : 0<n := by omega
    have hdiv := Nat.div_lt_self hn (show 1<4 by decide)
    simp only [children,if_neg h0,if_neg h1,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hdiv
    · exact (Nat.unpair_right_le _).trans_lt hdiv
  · intro n
    rw [PolicyFinite.finiteScalarCode]
    have hm4 : n%4<4 := Nat.mod_lt _ (by decide)
    by_cases h0 : n%4=0
    · simp [children,assemble,h0]
    by_cases h1 : n%4=1
    · simp [children,assemble,h0,h1]
    have h23 : n%4=2 ∨ n%4=3 := by omega
    simp [children,assemble,h0,h1,h23]

theorem coefficient_check : PolicyFiniteTargets.CoefficientCheck := ⟨checker_primitive.to_comp,check_exact⟩
end LogicLineages.StandardControlCurrent.PolicyFiniteProof
