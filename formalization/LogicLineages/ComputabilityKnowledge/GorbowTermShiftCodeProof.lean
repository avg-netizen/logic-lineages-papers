module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermShiftCode
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof
open GorbowSyntax GorbowSyntaxValidation GorbowTermShiftCode

theorem scannerInvariant : Comparators.GorbowTermShiftCode.ScannerInvariant := by
  intro n b t
  induction t with
  | var i =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, shiftStep, shiftedToken, step, expand, i.isLt,
        shiftTerm, GorbowFormulaSubstitution.renameTerm, GorbowSubstitution.substitute, shiftVar,
        List.append_assoc]
  | zero =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, shiftStep, shiftedToken, step, expand,
        shiftTerm, GorbowFormulaSubstitution.renameTerm, GorbowSubstitution.substitute]
  | succ t ih | universalFunction t ih =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, shiftStep, shiftedToken, step, expand, ih,
        shiftTerm, GorbowFormulaSubstitution.renameTerm, GorbowSubstitution.substitute, List.append_assoc]
  | add t u ht hu | mul t u ht hu =>
      intro tasks acc
      simp [GorbowTermPrefixCode.encode, List.foldl_append, shiftStep, shiftedToken, step, expand, ht, hu,
        shiftTerm, GorbowFormulaSubstitution.renameTerm, GorbowSubstitution.substitute, List.append_assoc]

private theorem rawEncode (n b : Nat) (t : Term n) :
    shiftRaw n b (GorbowTermPrefixCode.encode t) = GorbowTermPrefixCode.encode (shiftTerm b t) := by
  simpa [shiftRaw] using congrArg Prod.snd (scannerInvariant n b t [] [])

private theorem validEncode (n : Nat) (t : Term n) : validTerm n (GorbowTermPrefixCode.encode t) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.1 n _).mpr
    ⟨t, (GorbowTermPrefixCodeProof.decoderExact n _ t).mpr rfl⟩

private theorem codeEncode (n b : Nat) (t : Term n) :
    shiftCode n b (GorbowTermPrefixCode.encode t) = some (GorbowTermPrefixCode.encode (shiftTerm b t)) := by
  simp only [shiftCode, validEncode, ↓reduceIte, rawEncode]

theorem exactOutput : Comparators.GorbowTermShiftCode.ExactOutput := by
  intro n b raw out
  constructor
  · intro h
    have hv : validTerm n raw = true := by
      by_contra hv
      simp [shiftCode,hv] at h
    obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 n raw).mp hv
    have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp ht
    subst raw
    rw [codeEncode] at h
    exact ⟨t,rfl,(Option.some.inj h).symm⟩
  · rintro ⟨t,rfl,rfl⟩
    exact codeEncode n b t

theorem exactRejection : Comparators.GorbowTermShiftCode.ExactRejection := by
  intro n b raw
  constructor
  · intro h
    cases hd : GorbowTermPrefixCode.decode n raw with
    | none => rfl
    | some t =>
        have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp hd
        subst raw
        rw [codeEncode] at h
        cases h
  · intro hd
    have hv : validTerm n raw ≠ true := by
      intro h
      obtain ⟨t,ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 n raw).mp h
      rw [hd] at ht
      cases ht
    simp [shiftCode,hv]

theorem actualSemantics : Comparators.GorbowTermShiftCode.ActualSemantics := by
  intro n b t I v
  exact GorbowSubstitution.substitute_realize I v (fun i => Term.var (shiftVar n b i)) t

private theorem pr_shiftedList : Primrec (fun p : (Nat × Nat) × List Task =>
    match p.2 with
    | [] => p.1.2
    | task :: _ => if task.1 = 2 then p.1.2+p.1.1 else p.1.2) := by
  have hb : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have h := Primrec.list_casesOn Primrec.snd (Primrec.snd.comp Primrec.fst)
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 2)) (Primrec.nat_add.comp hx hb) hx).to₂
  apply h.of_eq
  intro p
  cases p.2 <;> rfl

private theorem pr_shiftedToken : Primrec (fun p : Nat × State × Nat => shiftedToken p.1 p.2.1 p.2.2) := by
  have h := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd : Primrec (fun p : Nat × State × Nat => p.2.1))
    (Primrec.snd.comp Primrec.snd)
    (pr_shiftedList.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨b,state,token⟩
  cases state with
  | none => rfl
  | some tasks => cases tasks <;> rfl

private theorem pr_shiftStep : Primrec (fun p : Nat × OutputState × Nat => shiftStep p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat × OutputState × Nat => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ho : Primrec (fun p : Nat × OutputState × Nat => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hx : Primrec (fun p : Nat × OutputState × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (GorbowSyntaxValidationProof.uniformPrograms.2.1.comp (hs.pair hx)).pair
    (Primrec.list_append.comp ho (Primrec.list_cons.comp
      (pr_shiftedToken.comp (Primrec.fst.pair (hs.pair hx))) (Primrec.const [])))

private theorem pr_shiftRaw : Primrec (fun p : Nat × Nat × List Nat => shiftRaw p.1 p.2.1 p.2.2) := by
  have hi : Primrec (fun p : Nat × Nat × List Nat => (some [(0,p.1)],([] : List Nat))) :=
    (Primrec.option_some.comp (Primrec.list_cons.comp ((Primrec.const 0).pair Primrec.fst)
      (Primrec.const []))).pair (Primrec.const [])
  have hb : Primrec (fun p : Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun p : Nat × Nat × List Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.snd.comp (Primrec.list_foldl hl hi (pr_shiftStep.comp ((hb.comp Primrec.fst).pair Primrec.snd)).to₂)

private theorem pr_shiftCode : Primrec (fun p : Nat × Nat × List Nat => shiftCode p.1 p.2.1 p.2.2) := by
  have hv := GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1.comp
    (Primrec.fst.pair (Primrec.snd.comp Primrec.snd) : Primrec (fun p : Nat × Nat × List Nat => (p.1,p.2.2)))
  exact Primrec.ite (Primrec.eq.comp hv (Primrec.const true)) (Primrec.option_some.comp pr_shiftRaw) (Primrec.const none)

theorem uniformPrograms : Comparators.GorbowTermShiftCode.UniformPrograms :=
  ⟨pr_shiftedToken,pr_shiftStep,pr_shiftRaw,pr_shiftCode⟩

theorem gorbowTermShiftCode : Comparators.GorbowTermShiftCode.Target :=
  ⟨scannerInvariant,exactOutput,exactRejection,actualSemantics,uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowTermShiftCodeProof
