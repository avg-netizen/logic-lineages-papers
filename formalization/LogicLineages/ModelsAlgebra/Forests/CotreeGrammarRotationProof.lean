module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotationTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpenStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.Proof
open CotreeGrammarOpen CotreeGrammarFlow CotreeGrammarFlow.Proof CotreeGrammarOpen.Proof

theorem composePlug : Targets.ComposePlug := by
  intro Q δ r q s C D t
  induction C with
  | hole => rfl
  | left C u ih => exact congrArg (fun v => Tree.branch v u) (ih D)
  | right u C ih => exact congrArg (fun v => Tree.branch u v) (ih D)

theorem composeCounts : Targets.ComposeCounts := by
  intro Q _ δ r q s C D
  unfold contextCounts
  rw [composePlug, plugCounts]
  rfl

theorem contextHolesLaw : Targets.ContextHolesLaw := by
  intro Q _ δ r q C t x
  induction C with
  | hole => simp [plug, contextHoles]
  | left C u ih => simp only [plug, holes, contextHoles, List.count_append, ih]; omega
  | right u C ih => simp only [plug, holes, contextHoles, List.count_append, ih]; omega

theorem fillCounts : Targets.FillCounts := by
  intro Q _ δ r x y C u v
  induction C with
  | @fork r s x y C D =>
    change nodeCounts r s (counts (plug C u)) (counts (plug D v)) =
      addCounts (addCounts (nodeCounts r s (contextCounts C) (contextCounts D)) (counts u)) (counts v)
    rw [plugCounts, plugCounts]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega
  | @forkSwap r s x y C D =>
    change nodeCounts r s (counts (plug C v)) (counts (plug D u)) =
      addCounts (addCounts (nodeCounts r s (contextCounts C) (contextCounts D)) (counts u)) (counts v)
    rw [plugCounts, plugCounts]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega
  | @left r s x y C t ih =>
    change nodeCounts r s (counts (fill C u v)) (counts t) =
      addCounts (addCounts (nodeCounts r s (twoCounts C) (counts t)) (counts u)) (counts v)
    rw [ih]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega
  | @right r s x y t C ih =>
    change nodeCounts r s (counts t) (counts (fill C u v)) =
      addCounts (addCounts (nodeCounts r s (counts t) (twoCounts C)) (counts u)) (counts v)
    rw [ih]
    apply countExt <;> intro p <;> simp only [nodeCounts, addCounts] <;> omega

theorem twoHolesLaw : Targets.TwoHolesLaw := by
  intro Q _ δ r x y C u v z
  induction C with
  | fork C D =>
    simp only [fill, holes, twoHoles, List.count_append]
    rw [contextHolesLaw, contextHolesLaw]
    omega
  | forkSwap C D =>
    simp only [fill, holes, twoHoles, List.count_append]
    rw [contextHolesLaw, contextHolesLaw]
    omega
  | left C t ih => simp only [fill, holes, twoHoles, List.count_append, ih]; omega
  | right t C ih => simp only [fill, holes, twoHoles, List.count_append, ih]; omega

theorem onPathRotation : Targets.OnPathRotation := by
  intro Q _ δ x y C D
  constructor
  · change contextCounts (compose C D) = contextCounts (compose D C)
    rw [composeCounts, composeCounts]
    apply countExt <;> intro p <;> simp only [addCounts] <;> omega
  · intro h
    apply List.perm_singleton.mp
    apply List.perm_iff_count.mpr
    intro z
    have ho := congrArg (List.count z) h
    rw [composePlug, contextHolesLaw, contextHolesLaw] at ho
    rw [composePlug, contextHolesLaw, contextHolesLaw]
    simp only [holes] at ho ⊢
    omega

theorem offPathRotation : Targets.OffPathRotation := by
  intro Q _ δ x y C D t
  constructor
  · rw [fillCounts, plugCounts, plugCounts, fillCounts]
    apply countExt <;> intro p <;> simp only [addCounts, counts, zeroCounts] <;> omega
  · intro h
    apply List.perm_singleton.mp
    apply List.perm_iff_count.mpr
    intro z
    have ho := congrArg (List.count z) h
    rw [twoHolesLaw, contextHolesLaw] at ho
    rw [contextHolesLaw, twoHolesLaw]
    simp only [holes] at ho ⊢
    omega

theorem occursPlug {Q : Type} {δ : Q → Q → Q} {r x} (C : Context δ r x) (t : Tree δ x) :
    Occurs x (plug C t) := by
  induction C with
  | hole => exact Occurs.root t
  | left C u ih => exact Occurs.left (ih t)
  | right u C ih => exact Occurs.right (ih t)

theorem occurrenceFactorization : Targets.OccurrenceFactorization := by
  intro Q δ r t x
  constructor
  · intro h
    induction h with
    | root u => exact ⟨.hole x, u, rfl⟩
    | @left r s l t h ih =>
      obtain ⟨C, u, he⟩ := ih
      exact ⟨.left C t, u, by simp only [plug, he]⟩
    | @right r s l t h ih =>
      obtain ⟨C, u, he⟩ := ih
      exact ⟨.right l C, u, by simp only [plug, he]⟩
  · rintro ⟨C, u, rfl⟩
    exact occursPlug C u

theorem occursCases {Q : Type} {δ : Q → Q → Q} {r x} {t : Tree δ r}
    (h : Occurs x t) : x = r ∨ (match t with
      | .branch l u => Occurs x l ∨ Occurs x u
      | _ => False) := by
  induction h with
  | root => exact Or.inl rfl
  | left h => exact Or.inr (Or.inl h)
  | right h => exact Or.inr (Or.inr h)

theorem contextDichotomy : Targets.ContextDichotomy := by
  intro Q δ r x C
  induction C with
  | hole x =>
    intro y h
    rcases occursCases h with h | h
    · subst y; exact Or.inl ⟨.hole x, .hole x, rfl⟩
    · exact h.elim
  | @left r s x C t ih =>
    intro y h
    rcases occursCases h with h | h
    · subst y; exact Or.inl ⟨.hole _, .left C t, rfl⟩
    · rcases h with h | h
      · rcases ih y h with ⟨P, S, he⟩ | ⟨D, u, he⟩
        · exact Or.inl ⟨.left P t, S, by rw [he]; rfl⟩
        · exact Or.inr ⟨.left D t, u, fun v => congrArg (fun z => Tree.branch z t) (he v)⟩
      · obtain ⟨D, u, he⟩ := (occurrenceFactorization Q δ s t y).mp h
        exact Or.inr ⟨.forkSwap C D, u, fun v => by simp only [plug, fill, he]⟩
  | @right r s x t C ih =>
    intro y h
    rcases occursCases h with h | h
    · subst y; exact Or.inl ⟨.hole _, .right t C, rfl⟩
    · rcases h with h | h
      · obtain ⟨D, u, he⟩ := (occurrenceFactorization Q δ r t y).mp h
        exact Or.inr ⟨.fork D C, u, fun v => by simp only [plug, fill, he]⟩
      · rcases ih y h with ⟨P, S, he⟩ | ⟨D, u, he⟩
        · exact Or.inl ⟨.right t P, S, by rw [he]; rfl⟩
        · exact Or.inr ⟨.right t D, u, fun v => congrArg (fun z => Tree.branch t z) (he v)⟩

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotation.Proof
