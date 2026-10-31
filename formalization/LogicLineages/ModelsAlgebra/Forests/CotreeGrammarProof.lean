module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.Proof

theorem rulesExact : Targets.RulesExact := by
  intro Q _ _ δ R
  simp [rules]

variable {Q : Type}

def symbolSem (δ : Q → Q → Q) : Symbol (Finset Q) Q → Language (Finset Q)
  | .terminal B => {[B]}
  | .nonterminal q => {w | Builds δ q w}

def sentenceSem (δ : Q → Q → Q) : List (Symbol (Finset Q) Q) → Language (Finset Q)
  | [] => 1
  | x :: xs => symbolSem δ x * sentenceSem δ xs

theorem sem_append (δ : Q → Q → Q) (u v : List (Symbol (Finset Q) Q)) :
    sentenceSem δ (u ++ v) = sentenceSem δ u * sentenceSem δ v := by
  induction u with
  | nil => simp [sentenceSem]
  | cons x xs ih => simp [sentenceSem, ih, mul_assoc]

theorem sem_terminals (δ : Q → Q → Q) (w : List (Finset Q)) :
    sentenceSem δ (w.map Symbol.terminal) = {w} := by
  induction w with
  | nil => ext x; change (x = []) ↔ x = []; rfl
  | cons B w ih =>
    ext x
    simp only [List.map_cons, sentenceSem, symbolSem, ih, Language.mem_mul]
    change (∃ a, a = [B] ∧ ∃ b, b = w ∧ a ++ b = x) ↔ x = B :: w
    simp [eq_comm]

theorem rule_sem [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (R : ContextFreeRule (Finset Q) Q) (hr : R ∈ rules δ) :
    sentenceSem δ R.output ≤ symbolSem δ (.nonterminal R.input) := by
  rcases (rulesExact Q δ R).mp hr with ⟨r,s,rfl⟩ | ⟨B,q,hq,rfl⟩
  · intro w hw
    simp only [binaryRule, sentenceSem, mul_one, symbolSem, Language.mem_mul,
      Set.mem_setOf_eq] at hw ⊢
    rcases hw with ⟨u,hu,v,hv,rfl⟩
    exact Builds.node hu hv
  · intro w hw
    simp only [terminalRule, sentenceSem, mul_one, symbolSem,
      Set.mem_singleton_iff, Set.mem_setOf_eq] at hw ⊢
    subst w
    exact Builds.leaf B q hq

theorem produces_sem [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (start : Q)
    {u v} (h : (grammar δ start).Produces u v) : sentenceSem δ v ≤ sentenceSem δ u := by
  change ∃ R : ContextFreeRule (Finset Q) Q, R ∈ rules δ ∧ R.Rewrites u v at h
  rcases h with ⟨R,hr,hs⟩
  rcases hs.exists_parts with ⟨p,q,rfl,rfl⟩
  simp only [sem_append, sentenceSem, mul_one]
  exact mul_le_mul' (mul_le_mul' le_rfl (rule_sem δ R hr)) le_rfl

theorem derives_sem [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (start : Q)
    {u v} (h : (grammar δ start).Derives u v) : sentenceSem δ v ≤ sentenceSem δ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ last ih => exact (produces_sem δ start last).trans ih

theorem build_derives [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (start : Q)
    {q w} (h : Builds δ q w) :
    (grammar δ start).Derives [.nonterminal q] (w.map Symbol.terminal) := by
  induction h with
  | leaf B q hq =>
    apply ContextFreeGrammar.Produces.single
    exact ⟨terminalRule q B, (rulesExact Q δ _).mpr (Or.inr ⟨B,q,hq,rfl⟩),
      ContextFreeRule.Rewrites.input_output⟩
  | @node r s u v hu hv ihu ihv =>
    have hfirst : (grammar δ start).Produces [.nonterminal (δ r s)]
        [.nonterminal r, .nonterminal s] :=
      ⟨binaryRule δ r s, (rulesExact Q δ _).mpr (Or.inl ⟨r,s,rfl⟩),
        ContextFreeRule.Rewrites.input_output⟩
    have hleft := ihu.append_right [.nonterminal s]
    have hright := ihv.append_left (u.map Symbol.terminal)
    simpa only [List.map_append] using hfirst.single.trans (hleft.trans hright)

theorem grammarLanguageExact : Targets.GrammarLanguageExact := by
  intro Q _ _ δ q w
  constructor
  · intro h
    have hs := derives_sem δ q h
    have hw : w ∈ sentenceSem δ (w.map Symbol.terminal) := by rw [sem_terminals]; rfl
    have := hs hw
    simpa only [sentenceSem, mul_one, symbolSem, Set.mem_setOf_eq, grammar] using this
  · exact build_derives δ q

theorem skeletonNonempty : Targets.SkeletonNonempty := by
  intro Q δ q w h
  induction h with
  | leaf => simp
  | node _ _ ih _ =>
    intro h
    exact ih (List.append_eq_nil_iff.mp h).1

theorem countPermutationExact : Targets.CountPermutationExact := by
  intro Q _ _ δ q children
  simp only [grammarLanguageExact Q δ, counts, List.perm_iff_count]

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammar.Proof
