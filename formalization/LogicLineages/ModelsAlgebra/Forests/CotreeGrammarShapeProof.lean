module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.Proof
open ForestParseRepresentationBinary ProfileAutomatonEncoding CotreeGrammar

variable {Q : Type}

theorem shape_builds (δ : Q → Q → Q) (s : Shape (Finset Q × Q)) (h : Valid s) :
    Builds δ (fold δ Prod.snd s) ((word s).map Prod.fst) := by
  induction s with
  | leaf x => exact Builds.leaf x.1 x.2 (h ())
  | node p q hp hq =>
    have hl : Valid p := fun x => h (.inl x)
    have hr : Valid q := fun x => h (.inr x)
    simpa only [fold, word, List.map_append] using Builds.node (hp hl) (hq hr)

theorem builds_shape (δ : Q → Q → Q) {q w} (h : Builds δ q w) :
    ∃ s : Shape (Finset Q × Q), Valid s ∧ fold δ Prod.snd s = q ∧
      (word s).map Prod.fst = w := by
  induction h with
  | leaf B q hq => exact ⟨.leaf (B,q), fun _ => hq, rfl, rfl⟩
  | node _ _ ihl ihr =>
    rcases ihl with ⟨p,hp,ep,wp⟩
    rcases ihr with ⟨q,hq,eq,wq⟩
    refine ⟨.node p q, ?_, ?_, ?_⟩
    · intro pos
      cases pos with
      | inl x => exact hp x
      | inr x => exact hq x
    · simp only [fold, ep, eq]
    · simp only [word, List.map_append, wp, wq]

theorem shapeLanguageExact : Targets.ShapeLanguageExact := by
  intro Q _ _ δ q w
  rw [CotreeGrammar.StatementChecks.grammarLanguageExact Q δ]
  constructor
  · exact builds_shape δ
  · rintro ⟨s,hs,rfl,rfl⟩
    exact shape_builds δ s hs

theorem graftRunExact : Targets.GraftRunExact := by
  intro M o I r s
  induction s with
  | leaf => rfl
  | node p q hp hq => simp only [graft, machineRun, fold, hp, hq]

theorem graftGrammarSound : Targets.GraftGrammarSound := by
  intro M _ o I r B s h
  rw [CotreeGrammar.StatementChecks.grammarLanguageExact M.State (M.node o)]
  induction s with
  | leaf i => exact Builds.leaf (B i) (machineRun M (r i)) (h i)
  | node p q hp hq =>
    simpa only [word, List.map_append, graft, machineRun] using Builds.node hp hq

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape.Proof
