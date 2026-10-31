module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBooleanStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.Proof
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open CotreePresburgerBoolean CotreePresburgerPullback FirstOrder

variable {Q R : Type} [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]

theorem product_step (A : Automaton Q) (B : Automaton R) o s n (v : Fin n → Q ×ₗ R) :
    ((product A B).node o s).Realize (wordCounts (List.ofFn v)) ↔
      (A.node o (ofLex s).1).Realize (wordCounts (List.ofFn (fun i => (ofLex (v i)).1))) ∧
      (B.node o (ofLex s).2).Realize (wordCounts (List.ofFn (fun i => (ofLex (v i)).2))) := by
  change (pullFormula (fun t : Q ×ₗ R => (ofLex t).1) (A.node o (ofLex s).1) ⊓
      pullFormula (fun t : Q ×ₗ R => (ofLex t).2) (B.node o (ofLex s).2)).Realize _ ↔ _
  rw [FirstOrder.Language.Formula.realize_inf,
    CotreePresburgerPullback.StatementChecks.pullWordExact Q (Q ×ₗ R),
    CotreePresburgerPullback.StatementChecks.pullWordExact R (Q ×ₗ R)]
  simp only [List.map_ofFn,Function.comp_def]

theorem run_projections (A : Automaton Q) (B : Automaton R) {C s}
    (h : Runs (product A B) C s) : Runs A C (ofLex s).1 ∧ Runs B C (ofLex s).2 := by
  induction h with
  | atom => exact ⟨Runs.atom,Runs.atom⟩
  | @node o n c v s children step ih =>
    have hs := (product_step A B o s (n+2) v).mp step
    exact ⟨Runs.node (fun i => (ofLex (v i)).1) _ (fun i => (ih i).1) hs.1,
      Runs.node (fun i => (ofLex (v i)).2) _ (fun i => (ih i).2) hs.2⟩

theorem paired_run (A : Automaton Q) (B : Automaton R) {C q r}
    (ha : Runs A C q) (hb : Runs B C r) : Runs (product A B) C (toLex (q,r)) := by
  induction ha generalizing r with
  | atom => cases hb; exact Runs.atom
  | @node o n c v q children step ih =>
    cases hb with
    | node w r childrenB stepB =>
      apply Runs.node (fun i => toLex (v i,w i)) (toLex (q,r)) (fun i => ih i (childrenB i))
      exact (product_step A B o (toLex (q,r)) (n+2) _).mpr ⟨step,stepB⟩

theorem productRunsExact : Targets.ProductRunsExact := by
  intro Q R _ _ _ _ A B C s
  constructor
  · exact run_projections A B
  · rintro ⟨ha,hb⟩
    exact paired_run A B ha hb

theorem productLanguageExact : Targets.ProductLanguageExact := by
  intro Q R _ _ _ _ A B C
  constructor
  · rintro ⟨hred,s,hs,ha⟩
    have hr := (productRunsExact Q R A B C s).mp hs
    have hac : A.accept (ofLex s).1 = true ∧ B.accept (ofLex s).2 = true := by
      simpa only [product,Bool.and_eq_true] using ha
    exact ⟨⟨hred,_,hr.1,hac.1⟩,⟨hred,_,hr.2,hac.2⟩⟩
  · rintro ⟨⟨hred,q,hq,hqa⟩,⟨_,r,hr,hra⟩⟩
    refine ⟨hred,toLex (q,r),paired_run A B hq hr,?_⟩
    simp [product,hqa,hra]

theorem productComplete : Targets.ProductComplete := by
  intro Q R _ _ _ _ A B ha hb C hred
  obtain ⟨q,hq,huq⟩ := ha C hred
  obtain ⟨r,hr,hur⟩ := hb C hred
  refine ⟨toLex (q,r),paired_run A B hq hr,?_⟩
  intro s hs
  have hparts := (productRunsExact Q R A B C s).mp hs
  change ofLex s = (q,r)
  exact Prod.ext (huq _ hparts.1) (hur _ hparts.2)

theorem differenceLanguageExact : Targets.DifferenceLanguageExact := by
  intro Q R _ _ _ _ A B hdet C
  rw [difference,productLanguageExact Q R A (complement B) C,
    CotreePresburgerBoolean.StatementChecks.complementLanguageExact R B hdet C]
  constructor
  · rintro ⟨ha,_,hn⟩; exact ⟨ha,hn⟩
  · rintro ⟨ha,hn⟩; exact ⟨ha,ha.1,hn⟩

theorem inclusionToEmpty : Targets.InclusionToEmpty := by
  intro Q R _ _ _ _ A B hdet
  constructor
  · intro hin C hc
    have hh := (differenceLanguageExact Q R A B hdet C).mp hc
    exact hh.2 (hin C hh.1)
  · intro hem C ha
    classical
    by_contra hb
    exact hem C ((differenceLanguageExact Q R A B hdet C).mpr ⟨ha,hb⟩)

theorem complete_transport (T : Type) (d e : DecidableEq T) (A : Automaton T)
    (h : @CompleteDeterministic T d A) : @CompleteDeterministic T e A := by
  cases Subsingleton.elim d e
  exact h

theorem inclusion_transport (T U : Type) (d e : DecidableEq T) (f g : DecidableEq U)
    (A : Automaton T) (B : Automaton U) :
    (∀ C, @Language T d A C → @Language U f B C) ↔
      (∀ C, @Language T e A C → @Language U g B C) := by
  cases Subsingleton.elim d e
  cases Subsingleton.elim f g
  rfl

theorem sourceInclusionToEmpty : Targets.SourceInclusionToEmpty := by
  intro M N _ _
  have h := inclusionToEmpty _ _ (source M) (source N)
    (complete_transport _ _ _ _ (CotreePresburgerBoolean.StatementChecks.sourceComplete N))
  exact (inclusion_transport _ _ _ _ _ _ _ _).trans h

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct.Proof
