module
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixProof
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionProof
open Turing PredictionFiniteAlphabet PredictionNumericPrefix PredictionNumericPrefixExecution
open PredictionNumericPrefixExecutionTargets

private theorem prefix_machine (p : Table) (q : Nat) (word : List Nat)
    (h : p.2.2.length ≤ q * width p) (r : Nat) (hr : r < 2 * word.length) (a : Fin (width p)) :
    PredictionNumericPrefix.machine p q word (q + r) a =
      some ((prefixEntry p q word r).1, actionStmt p (prefixEntry p q word r).2) := by
  change (lookup (assembled p q word) (q + r) a.val).map _ = _
  rw [PredictionNumericPrefixProof.exactPrefixLookup p q word h r a.val hr]
  rfl

private theorem odd_entry (p : Table) (q : Nat) (word : List Nat) (n : Nat) :
    prefixEntry p q word (2 * n + 1) = (q + 2 * n, .inl false) := by
  have hm : (2 * n + 1) % 2 = 1 := by omega
  simp only [prefixEntry, hm, if_pos rfl]
  congr 1

private theorem even_entry (p : Table) (q : Nat) (word : List Nat) (n : Nat) :
    prefixEntry p q word (2 * n) = (entryState p q n, .inr (word.getI n)) := by
  have hm : (2 * n) % 2 = 0 := by omega
  have hd : (2 * n) / 2 = n := by omega
  simp only [prefixEntry, hm, Nat.zero_ne_one, ↓reduceIte, hd]
  by_cases hn : n = 0
  · subst n; simp [entryState]
  · have h2 : 2 * n ≠ 0 := by omega
    simp [entryState, hn, h2]

private theorem prefix_partial (p : Table) (q : Nat) (word : List Nat)
    (h : p.2.2.length ≤ q * width p) (n : Nat) (hn : n ≤ word.length)
    (xs : List (Fin (width p))) :
    Moves p q word (2 * n) ⟨entryState p q n, Tape.mk₁ xs⟩
      ⟨p.2.1, Tape.mk₁ ((word.take n).map (symbol p) ++ xs)⟩ := by
  induction n generalizing xs with
  | zero => simpa [entryState] using Moves.refl (p := p) (q := q) (word := word) (⟨p.2.1, Tape.mk₁ xs⟩)
  | succ n ih =>
    have hlt : n < word.length := by omega
    have he : entryState p q (n + 1) = q + (2 * n + 1) := by simp [entryState]; omega
    have hs₁ : TM0.step (PredictionNumericPrefix.machine p q word)
        ⟨entryState p q (n + 1), Tape.mk₁ xs⟩ =
        some ⟨q + 2 * n, (Tape.mk₁ xs).move .left⟩ := by
      rw [he]
      change (PredictionNumericPrefix.machine p q word (q + (2 * n + 1)) (Tape.mk₁ xs).head).map _ = _
      rw [prefix_machine p q word h _ (by omega), odd_entry]
      rfl
    have hs₂ : TM0.step (PredictionNumericPrefix.machine p q word)
        ⟨q + 2 * n, (Tape.mk₁ xs).move .left⟩ =
        some ⟨entryState p q n, Tape.mk₁ (symbol p (word.getI n) :: xs)⟩ := by
      change (PredictionNumericPrefix.machine p q word (q + 2 * n) ((Tape.mk₁ xs).move .left).head).map _ = _
      rw [prefix_machine p q word h _ (by omega), even_entry]
      simp [actionStmt, Tape.mk₁, Tape.mk₂]
    have ht : (word.take (n + 1)).map (symbol p) ++ xs =
        (word.take n).map (symbol p) ++ symbol p (word.getI n) :: xs := by
      rw [List.take_succ_eq_append_getElem hlt, List.getI_eq_getElem word hlt]
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append]
    rw [ht, show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    exact Moves.next hs₁ (Moves.next hs₂ (ih (by omega) _))

theorem exactPrefixTransitions : ExactPrefixTransitions := by
  intro p q word h xs
  simpa [PredictionNumericPrefixExecution.initial, prepared] using prefix_partial p q word h word.length le_rfl xs

private theorem moves_reaches {p : Table} {q : Nat} {word : List Nat} {n x y}
    (h : Moves p q word n x y) : StateTransition.Reaches (TM0.step (PredictionNumericPrefix.machine p q word)) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | next h _ ih => exact Relation.ReflTransGen.head h ih

private theorem respects_eq {α : Type} (f g : α → Option α) (S : α → Prop)
    (closed : ∀ x y, f x = some y → S x → S y) (step : ∀ x, S x → g x = f x) :
    StateTransition.Respects f g (fun x y => S x ∧ x = y) := by
  intro x _ hx
  obtain ⟨hx, rfl⟩ := hx
  cases he : f x with
  | none => exact (step x hx).trans he
  | some y => exact ⟨y, ⟨closed x y he hx, rfl⟩, Relation.TransGen.single ((step x hx).trans he)⟩

theorem exactBodyEvaluation : ExactBodyEvaluation := by
  intro p q word h hclosed x hx
  have hr := respects_eq (TM0.step (PredictionFiniteAlphabet.machine p))
    (TM0.step (PredictionNumericPrefix.machine p q word)) (fun y => y.q < q)
    (fun x y he hx => TM0.step_supports (PredictionFiniteAlphabet.machine p) hclosed he hx)
    (fun x hx => PredictionNumericPrefixProof.exactBodyStep p q word h x hx)
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz, he⟩ := StateTransition.tr_eval_rev hr ⟨hx, rfl⟩ hy
    rw [hz.2] at he
    exact he
  · intro hy
    obtain ⟨z, hz, he⟩ := StateTransition.tr_eval hr ⟨hx, rfl⟩ hy
    rw [← hz.2] at he
    exact he

theorem exactPrefixEvaluation : ExactPrefixEvaluation := by
  intro p q word h hs xs hstart
  rw [StateTransition.reaches_eval (moves_reaches (exactPrefixTransitions p q word h xs))]
  exact exactBodyEvaluation p q word h hs (prepared p word xs) hstart

theorem effectiveParameterFamily : EffectiveParameterFamily := by
  intro p q
  exact PredictionNumericPrefixProof.effectiveNumericAssembly.comp
    ((Primrec.const p).pair ((Primrec.const q).pair
      PredictionBinaryParameterLayoutProof.numericWordPrimitiveRecursive))

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixExecutionProof
