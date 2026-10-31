module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open ForwardTranslation

private theorem extraction_var (i j : Nat) : extractionLeaf (8*Nat.pair i j+3) =
    (none, some (4*i+1)) := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  have h1 : 8*Nat.pair i j+3≠1 := by omega
  have h2 : 8*Nat.pair i j+3≠2 := by omega
  simp [extractionLeaf, hm, hd, h1, h2]

theorem ordinalSyntaxExtractionCorrect : Targets.OrdinalSyntaxExtractionCorrect := by
  intro Γ t
  unfold extraction typedCode
  rw [ordinalSyntaxFoldCorrect]
  induction t with
  | zero => rfl
  | one => rfl
  | omega => rfl
  | var c =>
    rcases c with ⟨τ, v, j⟩
    simp [termFold, componentCode, extraction_var, extractPositive, compileScalar, scalarSyntaxCode]
  | add a b iha ihb =>
    simp only [termFold, iha, ihb]
    cases hpa : extractPositive a <;> cases hpb : extractPositive b <;>
      cases hsa : compileScalar a <;> cases hsb : compileScalar b <;>
      simp [extractionBranch, combineCodes, extractPositive, compileScalar, hpa, hpb, hsa, hsb,
        closedPositiveCode, scalarSyntaxCode]
  | emul a b iha ihb =>
    simp only [termFold, iha, ihb]
    cases hpa : extractPositive a <;> cases hpb : extractPositive b <;>
      simp [extractionBranch, combineCodes, extractPositive, compileScalar, hpa, hpb, closedPositiveCode]
  | collapse a b iha ihb =>
    simp only [termFold, iha, ihb]
    cases hpa : extractPositive a <;> cases hsb : compileScalar b <;>
      simp [extractionBranch, combineCodes, extractPositive, compileScalar, hpa, hsb, scalarSyntaxCode]

private theorem combine_primitive : Primrec (fun p : Nat × Option Nat × Option Nat => combineCodes p.1 p.2.1 p.2.2) := by
  apply Primrec.option_bind (Primrec.fst.comp Primrec.snd)
  change Primrec (fun q : (Nat × Option Nat × Option Nat) × Nat => do
    let y ← q.1.2.2
    pure (4 * Nat.pair q.2 y + q.1.1))
  have h : Primrec (fun q : (Nat × Option Nat × Option Nat) × Nat =>
      q.1.2.2.map (fun y => 4 * Nat.pair q.2 y + q.1.1)) := Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to₂
  apply h.of_eq
  intro q
  cases q.1.2.2 <;> rfl

theorem ordinalSyntaxExtractionPrimitiveRecursive : Targets.OrdinalSyntaxExtractionPrimitiveRecursive := by
  have hm : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hi := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hleaf : Primrec extractionLeaf :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const (some 0, some 4))
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const (some 1, none))
        (Primrec.ite (Primrec.eq.comp hm (Primrec.const 3))
          ((Primrec.const none).pair (Primrec.option_some.comp
            (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hi) (Primrec.const 1))))
          (Primrec.const (none, none))))
  have hb : Primrec (fun p : Nat × (Option Nat × Option Nat) × (Option Nat × Option Nat) => extractionBranch p.1 p.2.1 p.2.2) := by
    have ha : Primrec (fun p : Nat × (Option Nat × Option Nat) × (Option Nat × Option Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
    have hb : Primrec (fun p : Nat × (Option Nat × Option Nat) × (Option Nat × Option Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
    have hpp (k : Nat) := combine_primitive.comp ((Primrec.const k).pair
      ((Primrec.fst.comp ha).pair (Primrec.fst.comp hb)))
    have hss (k : Nat) := combine_primitive.comp ((Primrec.const k).pair
      ((Primrec.snd.comp ha).pair (Primrec.snd.comp hb)))
    have hps (k : Nat) := combine_primitive.comp ((Primrec.const k).pair
      ((Primrec.fst.comp ha).pair (Primrec.snd.comp hb)))
    exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4)) ((hpp 2).pair (hss 2))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5)) ((hpp 3).pair (Primrec.const none))
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6)) ((Primrec.const none).pair (hps 3))
          (Primrec.const (none, none))))
  exact ordinalSyntaxFoldPrimitiveRecursive _ _ _ hleaf hb
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
