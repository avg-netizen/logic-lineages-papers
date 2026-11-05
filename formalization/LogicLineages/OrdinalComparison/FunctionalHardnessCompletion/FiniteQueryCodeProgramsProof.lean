module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.FiniteQueryCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeProgramsProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair fallbackCode

theorem query_pr : Primrec (fun p : Bool × Nat × List Nat => queryCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Bool × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : Bool × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hs := PlainSystemCode.Proof.strict_pr.comp hn hr
  have hw := PlainSystemCode.Proof.weak_pr.comp hn hr
  have hp := Primrec.ite (Primrec.eq.comp (Primrec.fst (β := Nat × List Nat)) (Primrec.const true))
    ((Primrec.snd.comp hs).pair (Primrec.fst.comp hs)) hw
  exact Primrec.encode.comp
    ((PlainSystemCode.Proof.context_pr.comp hn hr).pair
      ((Primrec.fst.comp hp).pair (Primrec.snd.comp hp)))

attribute [local irreducible] queryCode

theorem queries_pr : Primrec (fun p : Bool × Nat × List Nat => queriesCode p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Bool × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm := MaskRestrictionCode.Proof.masks_pr.comp hn
  have hb : Primrec (fun p : (Bool × Nat × List Nat) × List Bool =>
      queryCode p.1.1 p.1.2.1 (MaskRestrictionCode.restrictRows p.2 p.1.2.2)) :=
    query_pr.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (MaskRestrictionCode.Proof.restrict_rows_pr.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
  exact Primrec.list_map hm hb.to₂

private theorem fallback_pr : Primrec fallbackCode := Primrec.dom_bool _
attribute [local irreducible] queriesCode SeededQueryCode.validSystem SeededInputCode.inputCode

theorem reduce_pr : Primrec₂ reduceCode := by
  have hb : Primrec (fun p : Bool × Nat => fallbackCode p.1) := fallback_pr.comp Primrec.fst
  have hs : Primrec (fun p : (Bool × Nat) × SystemCode =>
      if SeededQueryCode.validSystem p.2 then queriesCode p.1.1 p.2.1 (SeededInputCode.inputCode p.2)
      else fallbackCode p.1.1) :=
    Primrec.ite (Primrec.eq.comp (SeededQueryCode.Proof.valid_system_pr.comp Primrec.snd) (Primrec.const true))
      (queries_pr.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (SeededInputCode.Proof.input_pr.comp Primrec.snd))))
      (fallback_pr.comp (Primrec.fst.comp Primrec.fst))
  apply (Primrec.option_casesOn (Primrec.decode.comp Primrec.snd) hb hs.to₂).of_eq
  intro p
  unfold reduceCode
  cases Encodable.decode (α := SystemCode) p.2 <;> rfl

theorem primitivePrograms : Targets.PrimitivePrograms := ⟨query_pr, queries_pr, reduce_pr⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode.Proof
