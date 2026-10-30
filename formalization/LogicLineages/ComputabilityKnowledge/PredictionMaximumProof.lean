module

public import LogicLineages.ComputabilityKnowledge.PredictionMaximumTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionMaximumProof
open PredictionLearning PredictionCanonicalList PredictionMaximum PredictionMaximumTargets

private theorem prefix_rec (c : Code) (n : Nat) :
    Nat.rec (Nat.Partrec.Code.eval c 0)
      (fun j IH => IH.bind fun v => (Nat.Partrec.Code.eval c (j + 1)).bind fun w => Part.some (max v w)) n =
      prefixRun c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.rec_add_one, prefixRun, ih]

theorem prefixPartialRecursive : PrefixPartialRecursive := by
  have he : Partrec (fun z : (Code × Nat) × (Nat × Nat) =>
      Nat.Partrec.Code.eval z.1.1 (z.2.1 + 1)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.fst.comp Computable.fst)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))
  have hm : Computable₂ (fun z : (Code × Nat) × (Nat × Nat) => fun w : Nat => max z.2.2 w) :=
    (Primrec.nat_max.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp
  have hh := Partrec.bind he hm.partrec₂
  apply (Partrec.nat_rec Computable.snd
    (Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.const 0)) hh.to₂).of_eq
  intro z
  exact prefix_rec z.1 z.2

private theorem steps_rec (codes : List Code) (n k : Nat) :
    Nat.rec (Part.some 0)
      (fun j IH => IH.bind fun v => (prefixRun (codes.getD j Nat.Partrec.Code.zero) n).bind
        fun w => Part.some (max v w)) k = familySteps codes n k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Nat.rec_add_one, familySteps, ih]

private theorem steps_partrec : Partrec (fun z : List Code × Nat × Nat => familySteps z.1 z.2.1 z.2.2) := by
  have hc : Computable (fun z : (List Code × Nat × Nat) × (Nat × Nat) =>
      z.1.1.getD z.2.1 Nat.Partrec.Code.zero) :=
    ((Primrec.list_getD Nat.Partrec.Code.zero).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).to_comp
  have hn : Computable (fun z : (List Code × Nat × Nat) × (Nat × Nat) => z.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have he := prefixPartialRecursive.comp hc hn
  have hm : Computable₂ (fun z : (List Code × Nat × Nat) × (Nat × Nat) => fun w : Nat => max z.2.2 w) :=
    (Primrec.nat_max.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp
  apply (Partrec.nat_rec (Computable.snd.comp Computable.snd) (Computable.const 0).partrec
    (Partrec.bind he hm.partrec₂).to₂).of_eq
  intro z
  exact steps_rec z.1 z.2.1 z.2.2

theorem familyPartialRecursive : FamilyPartialRecursive :=
  steps_partrec.comp (Computable.fst.pair
    (Computable.snd.pair (Computable.list_length.comp Computable.fst)))

private theorem eval_value (c : Code) (hc : TotalNat c) (n : Nat) :
    Nat.Partrec.Code.eval c n = Part.some (evalValue c n) := by
  have hd : (Nat.Partrec.Code.eval c n).Dom := Part.dom_iff_mem.mpr (hc n)
  rw [evalValue, dif_pos hd]
  exact (Part.some_get hd).symm

private theorem sup_range_succ (f : Nat → Nat) (n : Nat) :
    (Finset.range (n + 1)).sup f = max ((Finset.range n).sup f) (f n) := by
  rw [Finset.range_add_one, Finset.sup_insert]
  exact Nat.max_comm _ _

private theorem prefix_value (c : Code) (hc : TotalNat c) (n : Nat) :
    prefixRun c n = Part.some ((Finset.range (n + 1)).sup (evalValue c)) := by
  induction n with
  | zero => simpa [prefixRun] using eval_value c hc 0
  | succ n ih =>
      rw [prefixRun, ih, eval_value c hc, sup_range_succ (evalValue c) (n + 1)]
      simp only [Part.bind_some]

private theorem steps_value (codes : List Code) (hc : ∀ c ∈ codes, TotalNat c) (n k : Nat)
    (hk : k ≤ codes.length) :
    familySteps codes n k = Part.some ((Finset.range k).sup fun i =>
      (Finset.range (n + 1)).sup fun j => evalValue (codes.getD i Nat.Partrec.Code.zero) j) := by
  induction k with
  | zero => simp [familySteps]
  | succ k ih =>
      have hkl : k < codes.length := by omega
      have ht : TotalNat (codes.getD k Nat.Partrec.Code.zero) := by
        apply hc
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl, Option.getD_some] using
          List.getElem_mem hkl
      rw [familySteps, ih (by omega), prefix_value _ ht,
        sup_range_succ (fun i => (Finset.range (n + 1)).sup fun j =>
          evalValue (codes.getD i Nat.Partrec.Code.zero) j) k]
      simp only [Part.bind_some]

theorem totalMaximumSemantics : TotalMaximumSemantics := by
  intro codes hc n
  exact steps_value codes hc n codes.length le_rfl

private theorem unpaired_partrec : Partrec (fun z : Nat =>
    familyRun ((Encodable.decode (α := List Code) z.unpair.1).getD []) z.unpair.2) := by
  exact familyPartialRecursive.comp
    ((Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const [])).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp

private theorem compiler_semantics (u : Code)
    (hu : Nat.Partrec.Code.eval u = fun z =>
      familyRun ((Encodable.decode (α := List Code) z.unpair.1).getD []) z.unpair.2) :
    CompilerSemantics u := by
  intro codes n
  rw [compileMaximum, Nat.Partrec.Code.eval_curry, hu]
  simp only [Nat.unpair_pair, Encodable.encodek, Option.getD_some]

private theorem compiler_computable (u : Code) : Computable (compileMaximum u) :=
  (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode).to_comp

private theorem compiler_total (u : Code) (hu : CompilerSemantics u) (codes : List Code)
    (hc : ∀ c ∈ codes, TotalNat c) : TotalNat (compileMaximum u codes) := by
  intro n
  refine ⟨maximumValue codes n, ?_⟩
  rw [hu, totalMaximumSemantics codes hc]
  exact Part.mem_some_iff.mpr rfl

theorem uniformMaximumCompiler : UniformMaximumCompiler := by
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp unpaired_partrec)
  have hs := compiler_semantics u hu
  refine ⟨u, compiler_computable u, hs, fun codes hc => ⟨compiler_total u hs codes hc, ?_⟩⟩
  intro n
  exact (hs codes n).trans (totalMaximumSemantics codes hc n)

private theorem canonical_total (m : Nat) : ∀ c ∈ canonicalPrefix m, TotalNat c := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact (PredictionCanonicalListProof.strictCanonicalEnumeration.2 i).1

private theorem canonical_maximum (m n : Nat) : maximumValue (canonicalPrefix m) n = canonicalBound m n := by
  unfold maximumValue canonicalPrefix canonicalBound
  simp only [List.length_map, List.length_range]
  apply Finset.sup_congr rfl
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range him,
    Option.map_some, Option.getD_some]

theorem canonicalOrdinaryBounds : CanonicalOrdinaryBounds := by
  intro u hu m hm
  refine ⟨compiler_total u hu _ (canonical_total m), fun n => ?_⟩
  rw [hu, totalMaximumSemantics _ (canonical_total m), canonical_maximum]

theorem canonicalBoundDominance : CanonicalBoundDominance := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n i j hi hj
    have hinner : evalValue (canonicalCode i) j ≤
        (Finset.range (n + 1)).sup (evalValue (canonicalCode i)) :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    have houter : (Finset.range (n + 1)).sup (evalValue (canonicalCode i)) ≤ canonicalBound m n :=
      Finset.le_sup (f := fun i => (Finset.range (n + 1)).sup (evalValue (canonicalCode i)))
        (Finset.mem_range.mpr hi)
    exact hinner.trans houter
  · intro n a b hab
    exact Finset.sup_mono (Finset.range_mono hab)
  · intro m a b hab
    exact Finset.sup_mono_fun (fun i hi => Finset.sup_mono (Finset.range_mono (by omega)))

end LogicLineages.ComputabilityKnowledge.PredictionMaximumProof
