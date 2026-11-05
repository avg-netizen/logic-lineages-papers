module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair fallbackCode

theorem valid_row_pr : Primrec₂ validRow :=
  Primrec.list_foldr Primrec.snd (Primrec.const true)
    (Primrec.and.comp
      (SeededInputCode.Proof.valid_pr.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂

theorem valid_system_pr : Primrec validSystem :=
  Primrec.list_foldr Primrec.snd (Primrec.const true)
    (Primrec.and.comp
      (valid_row_pr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem query_pr : Primrec (fun p : Bool × Nat × List Nat => queryCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Bool × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : Bool × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs := SeededSystemCode.Proof.strict_pr.comp hn hr
  have hw := SeededSystemCode.Proof.weak_pr.comp hn hr
  have hp := Primrec.ite (Primrec.eq.comp (Primrec.fst (β := Nat × List Nat)) (Primrec.const true))
    ((Primrec.snd.comp hs).pair (Primrec.fst.comp hs)) hw
  exact Primrec.encode.comp
    ((SeededSystemCode.Proof.context_pr.comp hn hr).pair
      ((Primrec.fst.comp hp).pair (Primrec.snd.comp hp)))

private theorem fallback_pr : Primrec fallbackCode := Primrec.dom_bool _

attribute [local irreducible] queryCode validSystem SeededInputCode.inputCode

theorem reduce_pr : Primrec₂ reduceCode := by
  have hb : Primrec (fun p : Bool × Nat => fallbackCode p.1) := fallback_pr.comp Primrec.fst
  have hs : Primrec (fun p : (Bool × Nat) × SystemCode =>
      if validSystem p.2 then queryCode p.1.1 p.2.1 (SeededInputCode.inputCode p.2)
      else fallbackCode p.1.1) :=
    Primrec.ite (Primrec.eq.comp (valid_system_pr.comp Primrec.snd) (Primrec.const true))
      (query_pr.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (SeededInputCode.Proof.input_pr.comp Primrec.snd))))
      (fallback_pr.comp (Primrec.fst.comp Primrec.fst))
  apply (Primrec.option_casesOn (Primrec.decode.comp Primrec.snd) hb hs.to₂).of_eq
  intro p
  unfold reduceCode
  cases Encodable.decode (α := SystemCode) p.2 <;> rfl

theorem primitivePrograms : Targets.PrimitivePrograms :=
  ⟨valid_row_pr, valid_system_pr, query_pr, reduce_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode.Proof
