module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem leaf_free (i j : Nat) : headLeafFree (8*Nat.pair i j+3) = decide (i≠0) := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  simp [headLeafFree, hm, hd]

private theorem leaf_closure (i j : Nat) : headLeafClosure (8*Nat.pair i j+3) =
    if i=0 then 1 else 8*Nat.pair (i-1) j+3 := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  simp [headLeafClosure, hm, hd]

theorem ordinalSyntaxHeadFreeCorrect : Targets.OrdinalSyntaxHeadFreeCorrect := by
  intro Γ σ t
  unfold headFree typedCode
  rw [ordinalSyntaxFoldCorrect]
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> simp [termFold, componentCode, SourceTypedPorts.variableIndex, leaf_free,
      ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb => simp [termFold, iha, ihb, ordinalHeadFree, ordinalHeadOccurs]
  | emul a b iha ihb => simp [termFold, iha, ihb, ordinalHeadFree, ordinalHeadOccurs]
  | collapse a b iha ihb => simp [termFold, iha, ihb, ordinalHeadFree, ordinalHeadOccurs]

theorem ordinalSyntaxHeadClosureCorrect : Targets.OrdinalSyntaxHeadClosureCorrect := by
  intro Γ σ t
  unfold headClosure typedCode
  rw [ordinalSyntaxFoldCorrect]
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> simp [termFold, componentCode, SourceTypedPorts.variableIndex, leaf_closure,
      ordinalHeadClosure, substitute, ordinalHeadClosureComponent, code]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb => simp [termFold, iha, ihb, ordinalHeadClosure, substitute, code] at *
  | emul a b iha ihb => simp [termFold, iha, ihb, ordinalHeadClosure, substitute, code] at *
  | collapse a b iha ihb => simp [termFold, iha, ihb, ordinalHeadClosure, substitute, code] at *

private theorem size_data (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ::Γ)) :
    headSizeData (typedCode t) = (ordinalHeadFree t, ordinalPartialSize t) := by
  unfold headSizeData typedCode
  rw [ordinalSyntaxFoldCorrect]
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> simp [termFold, componentCode, SourceTypedPorts.variableIndex, leaf_free,
      ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs, ordinalPartialSize]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp only [termFold, iha, ihb]
    simp [ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs]
  | emul a b iha ihb =>
    simp only [termFold, iha, ihb]
    simp [ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs]
  | collapse a b iha ihb =>
    simp only [termFold, iha, ihb]
    simp [ordinalPartialSize, ordinalHeadFree, ordinalHeadOccurs]

theorem ordinalSyntaxPartialSizeCorrect : Targets.OrdinalSyntaxPartialSizeCorrect := by
  intro Γ σ t
  exact congrArg Prod.snd (size_data Γ σ t)

theorem ordinalSyntaxHeadOperationsPrimitiveRecursive : Targets.OrdinalSyntaxHeadOperationsPrimitiveRecursive := by
  have hm : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hi := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hj := Primrec.snd.comp (Primrec.unpair.comp hd)
  have he : PrimrecPred (fun n : Nat => n%8=3) := Primrec.eq.comp hm (Primrec.const 3)
  have hz : PrimrecPred (fun n : Nat => (n/8).unpair.1=0) := Primrec.eq.comp hi (Primrec.const 0)
  have hfree : Primrec headLeafFree := Primrec.ite he hz.not.decide (Primrec.const true)
  have hclosure : Primrec headLeafClosure :=
    Primrec.ite he (Primrec.ite hz (Primrec.const 1)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
        (Primrec₂.natPair.comp (Primrec.nat_sub.comp hi (Primrec.const 1)) hj)) (Primrec.const 3))) Primrec.id
  have hfreebranch : Primrec (fun p : Nat × Bool × Bool => p.2.1 && p.2.2) :=
    Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hclosurebranch : Primrec (fun p : Nat × Nat × Nat => 8*Nat.pair p.2.1 p.2.2+p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))) Primrec.fst
  refine ⟨ordinalSyntaxFoldPrimitiveRecursive _ _ _ hfree hfreebranch,
    ordinalSyntaxFoldPrimitiveRecursive _ _ _ hclosure hclosurebranch, ?_⟩
  have hleaf : Primrec (fun n : Nat => (headLeafFree n, 1)) := hfree.pair (Primrec.const 1)
  have hbranch : Primrec (fun p : Nat × (Bool × Nat) × (Bool × Nat) =>
      (p.2.1.1 && p.2.2.1, if p.2.1.1 && p.2.2.1 then 1 else
        (if p.1=5 then 2*p.2.1.2 else p.2.1.2)+p.2.2.2+1)) := by
    have ha : Primrec (fun p : Nat × (Bool × Nat) × (Bool × Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hb : Primrec (fun p : Nat × (Bool × Nat) × (Bool × Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
    have hf := Primrec.and.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)
    have hw := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp ha)) (Primrec.snd.comp ha)
    exact hf.pair (Primrec.ite (Primrec.eq.comp hf (Primrec.const true)) (Primrec.const 1)
      (Primrec.nat_add.comp (Primrec.nat_add.comp hw (Primrec.snd.comp hb)) (Primrec.const 1)))
  exact Primrec.snd.comp (ordinalSyntaxFoldPrimitiveRecursive _ _ _ hleaf hbranch)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
