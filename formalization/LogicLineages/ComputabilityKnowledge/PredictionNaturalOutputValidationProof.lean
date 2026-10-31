module
public import LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationProof
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinaryParameterLayout PredictionNaturalOutputValidation
open PredictionNaturalOutputValidationTargets

theorem exactBitValue : ExactBitValue := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n; simp [bits, value]
    have hd : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    rw [bits, dif_neg hz, value, ih _ hd]
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have he := Nat.mod_add_div n 2
    rcases hm with hm | hm <;> simp [hm] <;> omega

private theorem reverse_list (n : Nat) :
    (trList [n]).reverse = Γ'.cons :: (bits n).reverse.map bitSymbol := by
  have he := PredictionBinaryParameterLayoutProof.exactNaturalBits n
  simp [trList, ← he, List.reverse_append, List.map_reverse]

private theorem work_map (g : Γ') :
    (Function.update (fun _ : K' => none) K'.main (some g)) = slots (some g) none none none := by
  funext k
  cases k <;> simp [slots, Function.update]

theorem exactSourceTape : ExactSourceTape := by
  intro n
  unfold PredictionCompilerFiniteExecution.sourceInput TM2to1.trInit
  change (true, (((trList [n]).reverse.map
    (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).headI).2) ::
    (((trList [n]).reverse.map
      (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).tail) = _
  rw [reverse_list]
  simp only [List.map_cons, List.headI_cons, List.tail_cons, List.map_map, work_map]
  rfl

private theorem relation_functional {s : TM2.Cfg StackAlphabet Λ' Store}
    {x y : TM1.Cfg TapeAlphabet TapeLabel Store}
    (hx : TM2to1.TrCfg s x) (hy : TM2to1.TrCfg s y) : x = y := by
  cases hx with
  | mk L hL =>
    cases hy with
    | mk R hR =>
      have hLR : L = R := by
        apply ListBlank.ext
        intro n
        funext k
        have h := congrArg (fun t => t.nth n) ((hL k).trans (hR k).symm)
        simpa only [proj_map_nth] using h
      cases hLR
      rfl

private def track (g : Γ') : K' → Store := slots (some g) none none none

private theorem blank_map {α : Type} (ls : List α) :
    ListBlank.mk (ls.map (fun _ => (none : Store))) = ListBlank.mk [] := by
  apply ListBlank.ext
  intro n
  simp only [ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.getElem?_map]
  cases ls[n]? <;> rfl

private theorem canonical_relation (n : Nat) :
    TM2to1.TrCfg (PartrecToTM2.halt [n]) (outputConfig n) := by
  let L := ListBlank.mk ((Γ'.cons :: (bits n).reverse.map bitSymbol).map track)
  have hn := PredictionBinaryParameterLayoutProof.exactNaturalBits n
  have hb : ListBlank.mk (none :: List.replicate (bits n).length (none : Store)) = ListBlank.mk [] := by
    simpa [List.replicate_succ] using (blank_map (List.range ((bits n).length + 1)))
  have hproj : ∀ k : K', L.map (proj k) =
      ListBlank.mk (((K'.elim (trList [n]) [] [] []) k).map some).reverse := by
    intro k
    cases k <;> simp [L, track, slots, proj, K'.elim, ListBlank.map_mk, List.map_map,
      Function.comp_def, ← List.map_reverse, ← hn, hb]
  have hr : TM2to1.TrCfg (PartrecToTM2.halt [n])
      (⟨none, none, Tape.mk' ∅ (TM2to1.addBottom L)⟩ : TM1.Cfg TapeAlphabet TapeLabel Store) :=
    TM2to1.TrCfg.mk L hproj
  convert hr using 1
  simp only [outputConfig, outputSymbols, L, TM2to1.addBottom, List.map_cons,
    ListBlank.head_mk, List.headI_cons, ListBlank.tail_mk, List.tail_cons,
    ListBlank.map_mk, ListBlank.cons_mk, List.map_map]
  rfl

theorem exactSingletonLayout : ExactSingletonLayout := by
  intro n x
  constructor
  · intro h
    exact relation_functional h (canonical_relation n)
  · rintro rfl
    exact canonical_relation n

private theorem observed (bs : List Bool) :
    observe (Tape.mk₁ (bottomSymbol :: bs.map rawSymbol)) = recognize bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases b <;> cases bs with
    | nil => rfl
    | cons b' bs => cases b' <;> rfl

private theorem recognized_value (bs : List Bool) (b : Bool) (h : recognize bs = some b) :
    value bs.reverse = b.toNat := by
  cases bs with
  | nil => simp [recognize] at h; subst b; rfl
  | cons a bs =>
    cases a <;> cases bs <;> simp_all [recognize, value]

private theorem recognize_iff (n : Nat) (b : Bool) :
    recognize (bits n).reverse = some b ↔ n = b.toNat := by
  constructor
  · intro h
    have hv := recognized_value (bits n).reverse b h
    simpa only [List.reverse_reverse, exactBitValue n] using hv
  · intro h
    rw [h]
    cases b <;> simp [bits, recognize]

theorem exactBoundedObservation : ExactBoundedObservation := by
  intro n x b hx
  rw [(exactSingletonLayout n x).1 hx]
  change observe (Tape.mk₁ (bottomSymbol :: (bits n).reverse.map rawSymbol)) = some b ↔ _
  rw [observed]
  exact recognize_iff n b

end LogicLineages.ComputabilityKnowledge.PredictionNaturalOutputValidationProof
