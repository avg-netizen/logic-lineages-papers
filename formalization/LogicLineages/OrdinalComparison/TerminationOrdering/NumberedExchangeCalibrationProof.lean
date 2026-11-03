module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
  NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedAuxiliaryEnumeration
  NumberedFiniteUniverse NumberedExchangeNeighborhood NumberedExchangeCode
open NumberedAuxiliaryCodingProof NumberedAuxiliaryDecodingProof
  NumberedExchangeCalibrationSupportProof

theorem termSound {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (symbols : List Symbol) (S : List Ty) {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (upsilon : Ty) (r : AuxTerm Symbol arity Gamma upsilon), tau = upsilon →
      codeExchange arity symbols S (termCode q) (termCode r) = true →
        ∃ target, target ∈ neighbors symbols S q ∧
          (⟨tau, target⟩ : Packed Symbol arity Gamma) = ⟨upsilon, r⟩ := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ target : AuxArguments Symbol arity Gamma types,
      codeExchange arity symbols S (argumentsCode args) (argumentsCode target) = true →
        target ∈ argumentNeighbors symbols S args)
  case var =>
    intro upsilon r ht h
    cases r <;> simp [termCode, codeExchange] at h
  case bottom =>
    intro upsilon r ht h
    cases r <;> simp [termCode, codeExchange] at h
  case lam Gamma sigma tau body ih =>
    intro upsilon r ht h
    cases r <;> simp only [termCode, codeExchange] at h <;> try contradiction
    rename_i rho result other
    obtain ⟨hd, hr⟩ := Ty.arrow.inj ht
    cases hd
    cases hr
    have hc : codeExchange arity symbols S (termCode body) (termCode other) = true :=
      by simpa using h
    have hm := memberOfPackedWitness (ih _ other rfl hc)
    exact ⟨.lam other, List.mem_map.mpr ⟨other, hm, rfl⟩, rfl⟩
  case app Gamma sigma tau q a ihq iha =>
    intro upsilon r ht h
    cases r <;> simp only [termCode, codeExchange] at h <;> try contradiction
    rename_i rho function argument
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨hd, h⟩ := h
    cases hd
    cases ht
    rcases h with ⟨ha, hf⟩ | ⟨hf, ha⟩
    · have he := termCodeInjective Symbol arity Gamma sigma ha
      cases he
      have hm := memberOfPackedWitness (ihq _ _ rfl hf)
      exact ⟨.app _ a,
        List.mem_append_left _ (List.mem_map.mpr ⟨_, hm, rfl⟩), rfl⟩
    · have he := termCodeInjective Symbol arity Gamma (.arrow sigma tau) hf
      cases he
      have hm := memberOfPackedWitness (iha _ _ rfl ha)
      exact ⟨.app q _,
        List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, rfl⟩), rfl⟩
  case ordinary Gamma f base ih =>
    intro upsilon r ht h
    cases r <;> simp only [termCode, codeExchange] at h <;> try contradiction
    rename_i g other
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hmove, _⟩ | ⟨hhead, hargs⟩
    · obtain ⟨hf, hg, he, hp⟩ :=
        (headMoveCalibration symbols S f g base other).mp hmove
      obtain ⟨target, hm, heq⟩ :=
        ordinaryRootComplete symbols S f g base other hf hg he ht hp
      exact ⟨target, List.mem_append_left _ hm, heq⟩
    · have hf := headCodeInjective hhead
      cases hf
      have hm := ih other hargs
      exact ⟨.ordinary f other,
        List.mem_append_right _ (List.mem_map.mpr ⟨other, hm, rfl⟩), rfl⟩
  case numbered Gamma k f tau base types extras ihb ihe =>
    intro upsilon r ht h
    cases r <;> simp only [termCode, codeExchange] at h <;> try contradiction
    rename_i l g other otherTypes otherExtras
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hk, htau, htypes⟩, h⟩ := h
    cases hk
    cases htau
    cases htypes
    rcases h with h | h
    · rcases h with h | h
      · obtain ⟨hextras, hmove⟩ := h
        have he := argumentCodeInjective Symbol arity Gamma types hextras
        cases he
        obtain ⟨hf, hg, heq, hp⟩ :=
          (headMoveCalibration symbols S f g base _).mp hmove
        have hm := numberedRootComplete symbols S k f g tau base _ types extras
          hf hg heq hp
        exact ⟨.numbered k g tau _ types extras,
          List.mem_append_left _ (List.mem_append_left _ hm), rfl⟩
      · obtain ⟨⟨hhead, hextras⟩, hbase⟩ := h
        have hf := headCodeInjective hhead
        cases hf
        have he := argumentCodeInjective Symbol arity Gamma types hextras
        cases he
        have hm := ihb _ hbase
        exact ⟨.numbered k f tau _ types extras,
          List.mem_append_left _
            (List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, rfl⟩)), rfl⟩
    · obtain ⟨⟨hhead, hbase⟩, hextras⟩ := h
      have hf := headCodeInjective hhead
      cases hf
      have hb := argumentCodeInjective Symbol arity Gamma (headArguments arity f) hbase
      cases hb
      have hm := ihe _ hextras
      exact ⟨.numbered k f tau base types _,
        List.mem_append_right _ (List.mem_map.mpr ⟨_, hm, rfl⟩), rfl⟩
  case nil Gamma target h =>
    cases target
    simp [argumentsCode, codeExchange] at h
  case cons Gamma sigma types q rest ihq ihr target h =>
    cases target with
    | cons r tail =>
      simp only [argumentsCode, codeExchange, Bool.and_eq_true,
        Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨_, h⟩ := h
      rcases h with ⟨hrest, hq⟩ | ⟨hq, hrest⟩
      · have he := argumentCodeInjective Symbol arity Gamma types hrest
        cases he
        have hm := memberOfPackedWitness (ihq _ r rfl hq)
        exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hm, rfl⟩)
      · have he := termCodeInjective Symbol arity Gamma sigma hq
        cases he
        have hm := ihr tail hrest
        exact List.mem_append_right _ (List.mem_map.mpr ⟨tail, hm, rfl⟩)

theorem packedCalibration : NumberedExchangePrimrecTargets.ActualPackedCalibration := by
  intro Symbol inst arity Gamma symbols S q r
  apply Bool.eq_iff_iff.mpr
  simp only [packedCodeExchange, packedCode, Bool.and_eq_true, decide_eq_true_eq,
    NumberedExchangeNeighborhood.exchangeTest, List.mem_map]
  constructor
  · rintro ⟨ht, hc⟩
    exact termSound symbols S q.2 r.1 r.2 ht hc
  · rintro ⟨target, ht, he⟩
    cases he
    exact ⟨rfl, termComplete symbols S q.2 target ht⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationProof
