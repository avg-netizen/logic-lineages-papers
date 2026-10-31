module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBooleanTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.Proof
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree CotreePresburgerPullback

theorem source_counts (M : Machine) [LinearOrder M.State] n
    (v : Fin n → CotreePresburgerAutomaton.State M.State) :
    wordCounts (List.ofFn v) = fun a => (List.ofFn v).count a := by
  funext a
  exact CotreePresburgerPullback.StatementChecks.wordCountsEqCount _ _ a

theorem sourceRunsExact : Targets.SourceRunsExact := by
  intro M _ C q
  constructor
  · intro h
    induction h with
    | atom => exact CotreePresburgerAutomaton.Runs.atom
    | @node o n c v q children step ih =>
      change (CotreePresburgerAutomaton.nodeFormula M o q).Realize (wordCounts (List.ofFn v)) at step
      rw [source_counts] at step
      exact CotreePresburgerAutomaton.Runs.node v q ih step
  · intro h
    induction h with
    | atom => exact Runs.atom
    | @node o n c v q children step ih =>
      apply Runs.node v q ih
      change (CotreePresburgerAutomaton.nodeFormula M o q).Realize (wordCounts (List.ofFn v))
      rw [source_counts]
      exact step

theorem sourceLanguageExact : Targets.SourceLanguageExact := by
  intro M _ C
  constructor
  · rintro ⟨hred,q,hq,ha⟩
    exact (CotreePresburgerAutomaton.StatementChecks.acceptanceExact M C).mp
      ⟨q,(sourceRunsExact M C q).mp hq,ha⟩
  · intro h
    obtain ⟨q,hq,ha⟩ := (CotreePresburgerAutomaton.StatementChecks.acceptanceExact M C).mpr h
    exact ⟨h.1,q,(sourceRunsExact M C q).mpr hq,ha⟩

theorem sourceComplete : Targets.SourceComplete := by
  intro M _ C hred
  refine ⟨CotreePresburgerAutomaton.expected M C,?_,?_⟩
  · exact (sourceRunsExact M C _).mpr
      ((CotreePresburgerAutomaton.StatementChecks.runsExact M C _).mpr ⟨hred,rfl⟩)
  · intro q hq
    exact ((CotreePresburgerAutomaton.StatementChecks.runsExact M C q).mp
      ((sourceRunsExact M C q).mp hq)).2

theorem complementRunsExact : Targets.ComplementRunsExact := by
  intro Q _ A C q
  constructor
  · intro h
    induction h with
    | atom => exact Runs.atom
    | node v q _ step ih => exact Runs.node v q ih step
  · intro h
    induction h with
    | atom => exact Runs.atom
    | node v q _ step ih => exact Runs.node v q ih step

theorem complementLanguageExact : Targets.ComplementLanguageExact := by
  intro Q _ A hdet C
  constructor
  · rintro ⟨hred,q,hq,ha⟩
    refine ⟨hred,?_⟩
    rintro ⟨_,p,hp,hpa⟩
    obtain ⟨a,_,hunique⟩ := hdet C hred
    have hqa := hunique q ((complementRunsExact Q A C q).mp hq)
    have hpa' := hunique p hp
    have hqp : q = p := hqa.trans hpa'.symm
    have haq : A.accept q = true := by rw [hqp]; exact hpa
    change (!A.accept q) = true at ha
    rw [haq] at ha
    cases ha
  · rintro ⟨hred,hnot⟩
    obtain ⟨q,hq,_⟩ := hdet C hred
    refine ⟨hred,q,(complementRunsExact Q A C q).mpr hq,?_⟩
    change (!A.accept q) = true
    cases he : A.accept q with
    | false => rfl
    | true => exact (hnot ⟨hred,q,hq,he⟩).elim

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean.Proof
