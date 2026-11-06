module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionTargets
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceCodeProof
import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckPrimitiveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionCodeProof
open Source Source.SyntaxCode Admission

/-- The traversal retains the original numerical checker at every source node.
Its decreasing measure is the source code, not the context or the type bound. -/
theorem test_primitive : Primrec (fun s : Admission.Input => test s.1 s.2.1 s.2.2) := by
  let current : Admission.Input → Bool := fun s =>
    (check s.2.1 s.2.2).any (fun τ => decide (typeLevel τ ≤ s.1))
  let children : Admission.Input → List Admission.Input := fun s =>
    if s.2.2%8=5 then
      [(s.1,s.2.1,(s.2.2/8).unpair.1),(s.1,s.2.1,(s.2.2/8).unpair.2)]
    else if s.2.2%8=6 then
      [(s.1,(s.2.2/8).unpair.1::s.2.1,(s.2.2/8).unpair.2)] else []
  let assemble : Admission.Input → List Bool → Option Bool := fun s rs => some
    (current s &&
      if s.2.2%8=5 then rs.getD 0 false && rs.getD 1 false
      else if s.2.2%8=6 then rs.getD 0 false else true)
  have hΓ : Primrec (fun s : Admission.Input => s.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun s : Admission.Input => s.2.2) := Primrec.snd.comp Primrec.snd
  have htag : Primrec (fun s : Admission.Input => s.2.2%8) :=
    Primrec.nat_mod.comp hn (Primrec.const 8)
  have hpay : Primrec (fun s : Admission.Input => s.2.2/8) :=
    Primrec.nat_div.comp hn (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Admission.Input => s.2.2%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hcheck : Primrec (fun s : Admission.Input => check s.2.1 s.2.2) :=
    Source.SyntaxCode.Proof.checkPrimitiveRecursive.comp Primrec.snd
  have hbound : Primrec (fun p : Admission.Input × Nat =>
      decide (typeLevel p.2 ≤ p.1.1)) :=
    (Primrec.nat_le.comp
      (Source.SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide
  have hcurrent : Primrec current := by
    have h := Primrec.option_casesOn hcheck (Primrec.const false) hbound.to₂
    exact h.of_eq (fun s => by
      dsimp only [current]
      cases check s.2.1 s.2.2 <;> rfl)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair (hΓ.pair hl))
      (Primrec.list_cons.comp (Primrec.fst.pair (hΓ.pair hr)) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp
        (Primrec.fst.pair ((Primrec.list_cons.comp hl hΓ).pair hr)) (Primrec.const []))
      (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Admission.Input × List Bool => p.2.getD k false) :=
      (Primrec.list_getD false).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.and.comp (hcurrent.comp Primrec.fst)
      (Primrec.ite ((ht 5).comp Primrec.fst) (Primrec.and.comp (hg 0) (hg 1))
        (Primrec.ite ((ht 6).comp Primrec.fst) (hg 0) (Primrec.const true))))
  apply Primrec.nat_omega_rec' (fun s : Admission.Input => test s.1 s.2.1 s.2.2) hn hc ha
  · intro s t hmem
    change t.2.2 < s.2.2
    by_cases h5 : s.2.2%8=5
    · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2.2%8=6
      · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [Admission.test]
    have ht : s.2.2%8=0 ∨ s.2.2%8=1 ∨ s.2.2%8=2 ∨ s.2.2%8=3 ∨
        s.2.2%8=4 ∨ s.2.2%8=5 ∨ s.2.2%8=6 ∨ s.2.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,current,h]

theorem typedAccepts_primitive : Primrec Admission.typedAccepts := by
  have hc : Primrec (fun p : Admission.Input × Nat => check p.1.2.1 p.1.2.2) :=
    Source.SyntaxCode.Proof.checkPrimitiveRecursive.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.and.comp (test_primitive.comp Primrec.fst)
    (Primrec.eq.comp hc (Primrec.option_some.comp Primrec.snd)).decide

theorem accepts_primitive : Primrec Admission.accepts := by
  have hctx : Primrec (fun p : SourceCode.Input => List.replicate p.1 0) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.fst (β := Nat × Nat × Nat)))
      (Primrec.const (0 : Nat)).to₂
    exact h.of_eq (fun p => by simp)
  have ha : Primrec (fun p : SourceCode.Input => test 2 (List.replicate p.1 0) p.2.2.1) :=
    test_primitive.comp ((Primrec.const 2).pair
      (hctx.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
  have hb : Primrec (fun p : SourceCode.Input => test 2 (List.replicate p.1 0) p.2.2.2) :=
    test_primitive.comp ((Primrec.const 2).pair
      (hctx.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact Primrec.and.comp ha hb

theorem compile_primitive : Primrec Admission.compile := by
  exact Primrec.ite (Primrec.eq.comp accepts_primitive (Primrec.const true))
    SourceCodeProof.actualNumericProgram (Primrec.const none)

/-- Only the literal admission and guarded compiler programs are certified;
the emitted existential counterexample problem is not decided here. -/
theorem actualNumericPrograms : AdmissionTargets.ActualNumericPrograms :=
  ⟨test_primitive,typedAccepts_primitive,accepts_primitive,compile_primitive⟩
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionCodeProof
