module
public import LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingTargets
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeCodeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingProof
open PredictionAlphabetEmbedding PredictionAlphabetEmbeddingTargets

private theorem pr_liftTable : Primrec liftTable := by
  have hs : Primrec PredictionTapeTable.symbolIndex := by
    have hb : Primrec (fun b : Bool => if b then 2 else 1 : Bool → Nat) := Primrec.dom_bool _
    exact (Primrec.option_casesOn Primrec.id (Primrec.const 0) (hb.comp Primrec.snd).to₂).of_eq
      (fun a => by cases a with | none => rfl | some b => cases b <;> rfl)
  have ha : Primrec liftAction := by
    exact (Primrec.sumCasesOn Primrec.id
      (Primrec.sumInl.comp Primrec.snd).to₂
      (Primrec.sumInr.comp (hs.comp Primrec.snd)).to₂).of_eq
      (fun a => by cases a <;> rfl)
  have he : Primrec (fun x : Nat × PredictionTapeTable.Action => (x.1, liftAction x.2)) :=
    Primrec.fst.pair (ha.comp Primrec.snd)
  have ho : Primrec (fun o : Option (Nat × PredictionTapeTable.Action) =>
      o.map (fun x => (x.1, liftAction x.2))) :=
    Primrec.option_map Primrec.id (he.comp Primrec.snd).to₂
  exact (Primrec.const 0).pair (Primrec.fst.pair
    (Primrec.list_map Primrec.snd (ho.comp Primrec.snd).to₂))

theorem effectiveEmbedding : EffectiveEmbedding :=
  Primrec.encode.comp (pr_liftTable.comp PredictionTapeTableProof.effectiveDecoding.1)

private theorem lookup_lift (p : PredictionTapeTable.Table) (q : Nat)
    (a : PredictionTapeTable.Symbol) :
    PredictionFiniteAlphabet.lookup (liftTable p) q (PredictionTapeTable.symbolIndex a) =
      (PredictionTapeTable.lookup p q a).map (fun x => (x.1, liftAction x.2)) := by
  have ha : PredictionTapeTable.symbolIndex a < 3 := by
    cases a with | none => decide | some b => cases b <;> decide
  simp only [PredictionFiniteAlphabet.lookup, liftTable, PredictionFiniteAlphabet.width,
    Nat.zero_add, Nat.mod_eq_of_lt ha, List.getElem?_map, PredictionTapeTable.lookup]
  cases h : p.2[q * 3 + PredictionTapeTable.symbolIndex a]? with
  | none => rfl
  | some o => cases o <;> rfl

private theorem head_index (xs : List PredictionTapeTable.Symbol) :
    (xs.map PredictionTapeTable.symbolIndex).headI = PredictionTapeTable.symbolIndex xs.headI := by
  cases xs <;> rfl

private theorem execute_lift (q : Nat) (a : PredictionTapeTable.Action) (c : PredictionTapeTable.Raw) :
    PredictionFiniteAlphabet.execute q (liftAction a) (liftRaw c) =
      liftRaw (PredictionTapeTable.execute q a c) := by
  cases a with
  | inl b => cases b <;> simp [PredictionFiniteAlphabet.execute,
      PredictionTapeTable.execute, liftAction, liftRaw, head_index]
  | inr a => rfl

theorem exactStepEmbedding : ExactStepEmbedding := by
  intro p c
  unfold PredictionFiniteAlphabet.step PredictionTapeTable.step
  change (PredictionFiniteAlphabet.lookup (liftTable p) c.1 (PredictionTapeTable.symbolIndex c.2.1)).map _ = _
  rw [lookup_lift]
  simp only [Option.map_map]
  congr 1
  funext x
  exact execute_lift x.1 x.2 c

private theorem input_index (b : Bool) :
    PredictionTapeTable.symbolIndex (some b) = PredictionFiniteAlphabet.inputSymbol b := by
  cases b <;> rfl

private theorem initial_lift (p : PredictionTapeTable.Table) (xs : List Bool) :
    PredictionFiniteAlphabet.initial (liftTable p) xs = liftRaw (PredictionTapeTable.initial p xs) := by
  simp [PredictionFiniteAlphabet.initial, PredictionTapeTable.initial, liftTable,
    liftRaw, ← head_index, List.map_map, Function.comp_def, input_index]

private theorem bounded_lift (p : PredictionTapeTable.Table) (fuel : Nat) (c : PredictionTapeTable.Raw) :
    PredictionFiniteAlphabet.bounded (liftTable p) fuel (liftRaw c) =
      (PredictionTapeTable.bounded p fuel c).map liftRaw := by
  induction fuel generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PredictionFiniteAlphabet.bounded, PredictionTapeTable.bounded]
    rw [exactStepEmbedding p c]
    cases h : PredictionTapeTable.step p c with
    | none => rfl
    | some d => exact ih d

theorem exactSimulationEmbedding : ExactSimulationEmbedding := by
  intro code fuel xs
  unfold PredictionFiniteAlphabet.simulate liftCode
  rw [PredictionFiniteAlphabetProof.effectiveDecoding.2]
  rw [initial_lift, bounded_lift]
  rfl

theorem exactEvaderRuntime : ExactEvaderRuntime := by
  intro k xs fuel
  rw [exactSimulationEmbedding]
  have h := PredictionTapeCodeProof.exactCodedRuntime k xs fuel
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _⟩ := Option.map_eq_some_iff.mp hd
    exact h.1 ⟨c, hc⟩
  · intro hh
    obtain ⟨c, hc⟩ := h.2 hh
    exact ⟨liftRaw c, by rw [hc]; rfl⟩

theorem exactEvaderOutput : ExactEvaderOutput := by
  intro k xs fuel d h
  rw [exactSimulationEmbedding] at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  have hb := (PredictionTapeCodeProof.exactCodedOutput k xs fuel c hc).2
  by_cases hlt : xs.length < k <;> simp [liftRaw, hb, PredictionTapeTable.symbolIndex, hlt]

end LogicLineages.ComputabilityKnowledge.PredictionAlphabetEmbeddingProof
