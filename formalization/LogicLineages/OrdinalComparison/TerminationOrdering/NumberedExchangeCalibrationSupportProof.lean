module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
  NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedAuxiliaryEnumeration
  NumberedFiniteUniverse NumberedExchangeNeighborhood NumberedExchangeCode
open NumberedAuxiliaryCodingProof NumberedAuxiliaryDecodingProof
  NumberedExchangeNeighborhoodSupportProof

theorem argumentEntriesCalibration {Symbol : Type} {arity : Symbol → Nat}
    {Gamma types : List Ty} (args : AuxArguments Symbol arity Gamma types) :
    argumentEntries (argumentsCode args) = some ((argumentList args).map packedCode) := by
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih =>
    cases args with
    | cons q rest =>
      simp [argumentsCode, argumentEntries, argumentList, packedCode, ih rest]

theorem argumentPermutationCalibration {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma types otherTypes : List Ty}
    (args : AuxArguments Symbol arity Gamma types)
    (target : AuxArguments Symbol arity Gamma otherTypes) :
    argumentPermutation (argumentsCode args) (argumentsCode target) = true ↔
      (argumentList args).Perm (argumentList target) := by
  simp only [argumentPermutation, argumentEntriesCalibration, decide_eq_true_eq]
  exact List.map_perm_map_iff (packedCodeInjective Symbol arity Gamma)

theorem sourceHeadMembership {Symbol : Type} [DecidableEq Symbol]
    (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (g : Head Symbol) :
    headCode g ∈ sourceHeads arity symbols S ↔ g ∈ headWindow arity symbols S := by
  simp only [sourceHeads, List.mem_map]
  constructor
  · rintro ⟨f, hf, he⟩
    have hfg := headCodeInjective he
    exact hfg ▸ hf
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem headMoveCalibration {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (f g : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (target : AuxArguments Symbol arity Gamma (headArguments arity g)) :
    headMove arity symbols S (headCode f) (argumentsCode base)
        (headCode g) (argumentsCode target) = true ↔
      HeadInWindow arity symbols S f ∧ g ∈ headWindow arity symbols S ∧
        RecursiveComparison.headEquivalent f g ∧
          (argumentList base).Perm (argumentList target) := by
  simp only [headMove, Bool.and_eq_true, decide_eq_true_eq, headRoundTrip,
    sourceHeadMembership, argumentPermutationCalibration, and_assoc]

theorem termCodeCast {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (h : sigma = tau) (q : AuxTerm Symbol arity Gamma sigma) :
    termCode (h ▸ q) = termCode q := by
  cases h
  rfl

theorem ordinaryRootComplete {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (f g : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (target : AuxArguments Symbol arity Gamma (headArguments arity g))
    (hf : HeadInWindow arity symbols S f) (hg : g ∈ headWindow arity symbols S)
    (he : RecursiveComparison.headEquivalent f g) (ht : headResult f = headResult g)
    (hp : (argumentList base).Perm (argumentList target)) :
    ∃ r, r ∈ ordinaryNeighbors symbols S f base ∧
      (⟨headResult f, r⟩ : Packed Symbol arity Gamma) =
        ⟨headResult g, AuxTerm.ordinary g target⟩ := by
  refine ⟨ht.symm ▸ AuxTerm.ordinary g target, ?_, ?_⟩
  · simp only [ordinaryNeighbors, if_pos hf]
    apply List.mem_flatMap.mpr
    refine ⟨g, hg, ?_⟩
    simp only [if_pos he, dif_pos ht.symm]
    apply List.mem_filterMap.mpr
    exact ⟨argumentList target, List.mem_permutations.mpr hp.symm,
      by rw [listRoundTrip]; rfl⟩
  · exact packedCast ht.symm (AuxTerm.ordinary g target)

theorem numberedRootComplete {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (k : Nat) (f g : Head Symbol) (tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (target : AuxArguments Symbol arity Gamma (headArguments arity g))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types)
    (hf : HeadInWindow arity symbols S f) (hg : g ∈ headWindow arity symbols S)
    (he : RecursiveComparison.headEquivalent f g)
    (hp : (argumentList base).Perm (argumentList target)) :
    AuxTerm.numbered k g tau target types extras ∈
      numberedNeighbors symbols S k f tau base types extras := by
  simp only [numberedNeighbors, if_pos hf]
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  simp only [if_pos he]
  apply List.mem_filterMap.mpr
  exact ⟨argumentList target, List.mem_permutations.mpr hp.symm,
    by rw [listRoundTrip]; rfl⟩

theorem ordinaryRootCode {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (r : AuxTerm Symbol arity Gamma (headResult f))
    (h : r ∈ ordinaryNeighbors symbols S f base) :
    codeExchange arity symbols S (termCode (AuxTerm.ordinary f base)) (termCode r) =
      true := by
  simp only [ordinaryNeighbors] at h
  split at h
  next hf =>
    obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp h
    split at hr
    next he =>
      split at hr
      next ht =>
        obtain ⟨values, hv, hr⟩ := List.mem_filterMap.mp hr
        obtain ⟨target, ha, heq⟩ := Option.map_eq_some_iff.mp hr
        have hargs := listSound _ values target ha
        have hp := (List.mem_permutations.mp hv).symm
        rw [← hargs] at hp
        have hm := (headMoveCalibration symbols S f g base target).mpr
          ⟨hf, hg, he, hp⟩
        cases heq
        simp [termCodeCast, termCode, codeExchange, hm, headRoundTrip, ht]
      next => simp at hr
    next => simp at hr
  next => simp at h

theorem numberedRootCode {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} {Gamma : List Ty} (symbols : List Symbol) (S : List Ty)
    (k : Nat) (f : Head Symbol) (tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types)
    (r : AuxTerm Symbol arity Gamma tau)
    (h : r ∈ numberedNeighbors symbols S k f tau base types extras) :
    codeExchange arity symbols S
      (termCode (AuxTerm.numbered k f tau base types extras)) (termCode r) = true := by
  simp only [numberedNeighbors] at h
  split at h
  next hf =>
    obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp h
    split at hr
    next he =>
      obtain ⟨values, hv, hr⟩ := List.mem_filterMap.mp hr
      obtain ⟨target, ha, heq⟩ := Option.map_eq_some_iff.mp hr
      have hargs := listSound _ values target ha
      have hp := (List.mem_permutations.mp hv).symm
      rw [← hargs] at hp
      have hm := (headMoveCalibration symbols S f g base target).mpr
        ⟨hf, hg, he, hp⟩
      cases heq
      simp [termCode, codeExchange, hm]
    next => simp at hr
  next => simp at h

theorem termComplete {Symbol : Type} [DecidableEq Symbol]
    {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ r, r ∈ neighbors symbols S q →
      codeExchange arity symbols S (termCode q) (termCode r) = true := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => ∀ target,
      target ∈ argumentNeighbors symbols S args →
        codeExchange arity symbols S (argumentsCode args) (argumentsCode target) = true)
  case var => intro r h; simp [neighbors] at h
  case bottom => intro r h; simp [neighbors] at h
  case lam body ih =>
    intro r h
    obtain ⟨target, ht, he⟩ := List.mem_map.mp h
    cases he
    simp [termCode, codeExchange, ih target ht]
  case app q a ihq iha =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨target, ht, he⟩ := List.mem_map.mp h
      cases he
      simp [termCode, codeExchange, ihq target ht]
    · obtain ⟨target, ht, he⟩ := List.mem_map.mp h
      cases he
      simp [termCode, codeExchange, iha target ht]
  case ordinary f base ih =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · exact ordinaryRootCode symbols S f base r h
    · obtain ⟨target, ht, he⟩ := List.mem_map.mp h
      cases he
      simp [termCode, codeExchange, ih target ht]
  case numbered k f tau base types extras ihb ihe =>
    intro r h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact numberedRootCode symbols S k f tau base types extras r h
      · obtain ⟨target, ht, he⟩ := List.mem_map.mp h
        cases he
        simp [termCode, codeExchange, ihb target ht]
    · obtain ⟨target, ht, he⟩ := List.mem_map.mp h
      cases he
      simp [termCode, codeExchange, ihe target ht]
  case nil Gamma target h => simp [argumentNeighbors] at h
  case cons Gamma sigma types q rest ihq ihr target h =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r, hr, he⟩ := List.mem_map.mp h
      cases he
      simp [argumentsCode, codeExchange, ihq r hr]
    · obtain ⟨tail, ht, he⟩ := List.mem_map.mp h
      cases he
      simp [argumentsCode, codeExchange, ihr tail ht]

theorem memberOfPackedWitness {Symbol : Type} {arity : Symbol → Nat}
    {Gamma : List Ty} {tau : Ty} {values : List (AuxTerm Symbol arity Gamma tau)}
    {r : AuxTerm Symbol arity Gamma tau}
    (h : ∃ target, target ∈ values ∧
      (⟨tau, target⟩ : Packed Symbol arity Gamma) = ⟨tau, r⟩) : r ∈ values := by
  obtain ⟨target, ht, he⟩ := h
  have heq : target = r := eq_of_heq (Sigma.mk.inj he).2
  exact heq ▸ ht

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCalibrationSupportProof
