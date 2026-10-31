module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof

theorem typeDecodeEncode : Targets.TypeDecodeEncode := by
  intro τ
  induction τ with
  | ground => simp [typeCode,decodeType,typeLevel,Ty.level]
  | arrow a b ha hb => simp [typeCode, arrowCode, decodeType, Nat.unpair_pair, ha, hb]

theorem typeEncodeDecode : Targets.TypeEncodeDecode := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [typeCode,decodeType]
      | succ n =>
          rw [decodeType, typeCode, arrowCode,
            ih n.unpair.1 (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
            ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n)), Nat.pair_unpair]

theorem typeLevelExact : Targets.TypeLevelExact := by
  intro τ
  induction τ with
  | ground => simp [typeCode,decodeType,typeLevel,Ty.level]
  | arrow a b ha hb => simp [typeCode, arrowCode, typeLevel, Nat.unpair_pair, ha, hb, Ty.level]

theorem typeConstructorsPrimitiveRecursive : Targets.TypeConstructorsPrimitiveRecursive := by
  have ha : Primrec₂ arrowCode := Primrec.succ.comp Primrec₂.natPair
  refine ⟨ha, ?_, ?_⟩
  · exact ha.comp (Primrec.const 0) (ha.comp Primrec.id (ha.comp Primrec.id Primrec.id))
  · exact ha.comp (Primrec.const 0)
      (ha.comp (ha.comp (Primrec.const 0) (ha.comp Primrec.id Primrec.id))
        (ha.comp Primrec.id Primrec.id))

theorem typeLevelPrimitiveRecursive : Targets.TypeLevelPrimitiveRecursive := by
  let children : Nat → List Nat := fun n => if n=0 then [] else [(n-1).unpair.1,(n-1).unpair.2]
  let assemble : Nat → List Nat → Option Nat := fun n rs =>
    some (if n=0 then 0 else max (rs.getD 0 0 + 1) (rs.getD 1 0))
  have hz : PrimrecPred (fun n : Nat => n=0) := Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hp : Primrec (fun n : Nat => (n-1).unpair) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have hc : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.fst.comp hp)
      (Primrec.list_cons.comp (Primrec.snd.comp hp) (Primrec.const [])))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Nat × List Nat => p.2.getD k 0) :=
      (Primrec.list_getD 0).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (hz.comp Primrec.fst) (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.succ.comp (hg 0)) (hg 1)))
  apply Primrec.nat_omega_rec' typeLevel Primrec.id hc ha
  · intro n k hk
    change k < n
    by_cases hn : n=0
    · simp [children,hn] at hk
    have hl := Nat.unpair_left_le (n-1)
    have hr := Nat.unpair_right_le (n-1)
    simp only [children,if_neg hn,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl <;> omega
  · intro n
    cases n with
    | zero => simp [children,assemble,typeLevel]
    | succ n => simp [children,assemble,typeLevel]
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof
