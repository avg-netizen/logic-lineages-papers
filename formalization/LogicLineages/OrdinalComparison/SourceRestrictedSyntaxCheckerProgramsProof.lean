module
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof
attribute [local irreducible] Nat.unpair Nat.sqrt

private theorem fragment_primitive : Primrec fragmentCode := by
  let children : Nat → List Nat := fun n =>
    if n%8=5 then [(n/8).unpair.1,(n/8).unpair.2]
    else if n%8=6 then [(n/8).unpair.2] else []
  let assemble : Nat → List Bool → Option Bool := fun n rs => some
    (if n%8=0 then true else if n=1 ∨ n=2 then true else
      if n%8=5 then rs.getD 0 false && rs.getD 1 false else
      if n%8=6 then decide ((n/8).unpair.1=SyntaxCode.typeCode Ty.ground) && rs.getD 0 false
      else false)
  have htag : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hpay : Primrec (fun n : Nat => (n/8).unpair) :=
    Primrec.unpair.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  have ht (k : Nat) : PrimrecPred (fun n : Nat => n%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.comp hpay)
      (Primrec.list_cons.comp (Primrec.snd.comp hpay) (Primrec.const [])))
    (Primrec.ite (ht 6) (Primrec.list_cons.comp (Primrec.snd.comp hpay) (Primrec.const []))
      (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Nat × List Bool => p.2.getD k false) :=
      (Primrec.list_getD false).comp Primrec.snd (Primrec.const k)
    have h12 : PrimrecPred (fun p : Nat × List Bool => p.1=1 ∨ p.1=2) :=
      (Primrec.eq.comp Primrec.fst (Primrec.const 1)).or
        (Primrec.eq.comp Primrec.fst (Primrec.const 2))
    have hground : Primrec (fun p : Nat × List Bool =>
        decide ((p.1/8).unpair.1=SyntaxCode.typeCode Ty.ground)) :=
      (Primrec.eq.comp ((Primrec.fst.comp hpay).comp Primrec.fst)
        (Primrec.const (SyntaxCode.typeCode Ty.ground))).decide
    exact Primrec.option_some.comp (Primrec.ite ((ht 0).comp Primrec.fst) (Primrec.const true)
      (Primrec.ite h12 (Primrec.const true)
        (Primrec.ite ((ht 5).comp Primrec.fst) (Primrec.and.comp (hg 0) (hg 1))
          (Primrec.ite ((ht 6).comp Primrec.fst) (Primrec.and.comp hground (hg 0))
            (Primrec.const false)))))
  apply Primrec.nat_omega_rec' fragmentCode Primrec.id hc ha
  · intro n k hk
    change k<n
    by_cases h5 : n%8=5
    · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : n%8=6
      · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hk
        subst k
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hk
  · intro n
    conv_rhs => rw [fragmentCode]
    by_cases h5 : n%8=5
    · have h0 : n%8≠0 := by omega
      have h12 : ¬(n=1 ∨ n=2) := by omega
      simp [children,assemble,h5,h0,h12]
    · by_cases h6 : n%8=6
      · have h0 : n%8≠0 := by omega
        have h12 : ¬(n=1 ∨ n=2) := by omega
        simp [children,assemble,h5,h6,h0,h12]
      · simp [children,assemble,h5,h6]

private theorem ground_primitive : Primrec (fun p : Nat × Nat => groundCode p.1 p.2) := by
  have hctx : Primrec (fun p : Nat × Nat =>
      List.replicate p.1 (SyntaxCode.typeCode Ty.ground)) := by
    have hm : Primrec (fun p : Nat × Nat => (List.range p.1).map
        (fun _ => SyntaxCode.typeCode Ty.ground)) :=
      Primrec.list_map (Primrec.list_range.comp Primrec.fst)
        (Primrec.const (SyntaxCode.typeCode Ty.ground)).to₂
    exact hm.of_eq (fun p => by simp)
  have hcheck := SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair Primrec.snd)
  exact (Primrec.eq.comp hcheck (Primrec.const (some (SyntaxCode.typeCode Ty.ground)))).decide

private theorem restricted_primitive : Primrec restrictedCode := by
  have hb : Primrec (fun p : Nat × (Nat × Nat × Nat) =>
      groundCode p.2.1 p.2.2.1 && groundCode p.2.1 p.2.2.2 &&
        fragmentCode p.2.2.1 && fragmentCode p.2.2.2) := by
    have hn : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hl : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hr : Primrec (fun p : Nat × (Nat × Nat × Nat) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.and.comp (Primrec.and.comp
      (Primrec.and.comp (ground_primitive.comp (hn.pair hl)) (ground_primitive.comp (hn.pair hr)))
      (fragment_primitive.comp hl)) (fragment_primitive.comp hr)
  exact Primrec.option_casesOn SourceMachineQueryCode.Proof.unpack_primitive (Primrec.const false) hb.to₂

/-- Recognition uses only primitive-recursive raw-code operations. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨fragment_primitive,ground_primitive,restricted_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceRestrictedSyntaxChecker.Proof
