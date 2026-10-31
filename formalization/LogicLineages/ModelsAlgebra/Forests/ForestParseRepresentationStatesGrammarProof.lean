module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammarTargets
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrencesStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammar.Proof
open RankedParse ForestParseRepresentationCotree ForestParseRepresentationBinary
open ProfileAutomatonEncoding ForestParseRepresentationStates CotreeGrammarShape CotreeGrammarOccurrences

private theorem pairedRightCongr {I J Q : Type} {R : I → J → Prop}
    {s : Shape I} {t : Shape J} (f : I → Q) (g v : J → Q)
    (h : Paired (fun i j => R i j ∧ f i = g j) s t)
    (hv : ∀ p : Positions t, g (label t p) = v (label t p)) :
    Paired (fun i j => R i j ∧ f i = v j) s t := by
  induction h with
  | leaf h => exact Paired.leaf ⟨h.1, h.2.trans (hv ())⟩
  | node hl hr ihl ihr =>
    exact Paired.node (ihl (fun x => hv (.inl x))) (ihr (fun y => hv (.inr y)))

/-- Distinct target occurrences allow independent state choices to be assigned
back to actual child indices, without changing the ordered binary skeleton. -/
private theorem transferValues {I J Q : Type} {R : I → J → Prop}
    {s : Shape I} {t : Shape J} (h : Paired R s t) (f : I → Q)
    (hi : Function.Injective (label t)) :
    ∃ v : J → Q, Paired (fun i j => R i j ∧ f i = v j) s t := by
  classical
  induction h with
  | @leaf i j hr => exact ⟨fun _ => f i, Paired.leaf ⟨hr, rfl⟩⟩
  | @node p q r s hl hr ihl ihr =>
    have hil : Function.Injective (label r) := by
      intro x y hxy
      exact Sum.inl.inj (hi (a₁ := .inl x) (a₂ := .inl y) hxy)
    have hir : Function.Injective (label s) := by
      intro x y hxy
      exact Sum.inr.inj (hi (a₁ := .inr x) (a₂ := .inr y) hxy)
    obtain ⟨vl, hvl⟩ := ihl hil
    obtain ⟨vr, hvr⟩ := ihr hir
    let v : J → Q := fun j => if ∃ x : Positions r, label r x = j then vl j else vr j
    refine ⟨v, Paired.node (pairedRightCongr f vl v hvl ?_) (pairedRightCongr f vr v hvr ?_)⟩
    · intro x
      simp only [v, if_pos (show ∃ y : Positions r, label r y = label r x from ⟨x, rfl⟩)]
    · intro y
      have hn : ¬ ∃ x : Positions r, label r x = label s y := by
        rintro ⟨x, hx⟩
        have hbad := hi (a₁ := .inl x) (a₂ := .inr y) hx
        cases hbad
      simp only [v, if_neg hn]

private theorem pairedFold {I J Q : Type} {R : I → J → Prop}
    {s : Shape I} {t : Shape J} (h : Paired R s t)
    (δ : Q → Q → Q) (f : I → Q) (g : J → Q)
    (he : ∀ i j, R i j → f i = g j) : fold δ f s = fold δ g t := by
  induction h with
  | leaf h => exact he _ _ h
  | node _ _ ihl ihr => exact congrArg₂ δ ihl ihr

private theorem pairedAll {I J : Type} {R : I → J → Prop}
    {s : Shape I} {t : Shape J} (h : Paired R s t) (P : I → Prop) (S : J → Prop)
    (hp : ∀ x : Positions s, P (label s x)) (he : ∀ i j, R i j → P i → S j) :
    ∀ y : Positions t, S (label t y) := by
  induction h with
  | leaf h => intro y; exact he _ _ h (hp ())
  | node _ _ ihl ihr =>
    intro y
    cases y with
    | inl y => exact ihl (fun x => hp (.inl x)) y
    | inr y => exact ihr (fun x => hp (.inr x)) y

private theorem selectedBuilds {I Q : Type} (δ : Q → Q → Q) (B : I → Finset Q)
    (v : I → Q) (s : Shape I) (h : ∀ i, v i ∈ B i) :
    CotreeGrammar.Builds δ (fold δ v s) ((word s).map B) := by
  induction s with
  | leaf i => exact CotreeGrammar.Builds.leaf _ _ (h i)
  | node p q hp hq => simpa only [fold, word, List.map_append] using CotreeGrammar.Builds.node hp hq

theorem stateGrammarExact : Targets.StateGrammarExact := by
  intro M _ o n c q
  let B : Fin (n + 2) → Finset M.State := fun i => stateSet M (c i)
  constructor
  · intro h
    obtain ⟨s, v, hb, hv, hq⟩ := (ForestParseRepresentationStates.Proof.stateSetNodeExact M o n c q).mp h
    refine ⟨(word s).map B, ?_, ?_⟩
    · rw [CotreeGrammar.StatementChecks.grammarLanguageExact M.State (M.node o)]
      rw [← hq]
      exact selectedBuilds (M.node o) B v s hv
    · have hp := (CotreeGrammarOccurrences.Proof.occurrencePermutation (n + 2) s).mpr hb
      simpa only [List.ofFn_eq_map] using hp.map B
  · rintro ⟨w, hw, hp⟩
    obtain ⟨s, hs, hq, he⟩ := (CotreeGrammarShape.Proof.shapeLanguageExact M.State (M.node o) q w).mp hw
    have hp' : ((word s).map Prod.fst).Perm (List.ofFn B) := by simpa only [he] using hp
    obtain ⟨r, hr, hb⟩ := CotreeGrammarOccurrences.Proof.typeWordReindex
      (Finset M.State × M.State) (Finset M.State) (n + 2) Prod.fst B s hp'
    obtain ⟨v, hv⟩ := transferValues hr Prod.snd hb.1
    apply (ForestParseRepresentationStates.Proof.stateSetNodeExact M o n c q).mpr
    refine ⟨r, v, hb, ?_, ?_⟩
    · intro j
      obtain ⟨y, hy⟩ := hb.2 j
      have hall := pairedAll hv (fun i => i.2 ∈ i.1) (fun j => v j ∈ B j) hs
        (fun i j hij hi => by rw [← hij.1, ← hij.2]; exact hi)
      simpa only [hy] using hall y
    · exact (pairedFold hv (M.node o) Prod.snd v (fun _ _ h => h.2)).symm.trans hq

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesGrammar.Proof
