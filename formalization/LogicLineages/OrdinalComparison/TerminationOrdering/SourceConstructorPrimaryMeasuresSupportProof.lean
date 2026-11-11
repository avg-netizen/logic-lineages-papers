module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorSuppliersTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPrecedenceChainsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative RankedPrecedenceCertificate
open SourceZeroNumberedComputability SourceZeroNumberedShapeProof

/-- Root observations only; the source relation is unchanged. -/
def ordinaryShape {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Bool :=
  match q with
  | ⟨_,.ordinary _ _⟩ => true
  | _ => false

def constructorRank {n : Nat} {arity : Fin n → Nat} (rank : Fin n → Fin n)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : Option Nat :=
  match q with
  | ⟨_,.ordinary f _⟩ => some (headRank rank f)
  | ⟨_,.numbered _ f _ _ _ _⟩ => some (headRank rank f)
  | _ => none

def constructorBaseCodes {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : List (Ty × Nat) :=
  match q with
  | ⟨_,.ordinary _ base⟩ => argumentCodes symbols S base
  | ⟨_,.numbered _ _ _ base _ _⟩ => argumentCodes symbols S base
  | _ => []

def constructorExtraCodes {n : Nat} {arity : Fin n → Nat} (symbols : List (Fin n)) (S : List Ty)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) : List (Ty × Nat) :=
  match q with
  | ⟨_,.numbered _ _ _ _ _ extras⟩ => argumentCodes symbols S extras
  | _ => []

theorem primaryOrdinaryShape {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol}
    {S Gamma : List Ty} {q r : Packed Symbol arity Gamma}
    (h : WindowPrimary Symbol arity symbols S Gamma q r) : ordinaryShape q = ordinaryShape r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h k ih ik => exact ih.trans ik
  all_goals first | rfl | trivial

theorem primaryConstructorRank {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S : List Ty} (table : Fin n → Fin n → Bool) (rank : Fin n → Fin n)
    (hrank : rankCertificateTest table rank = true) {Gamma : List Ty}
    {q r : Packed (Fin n) arity Gamma} (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    constructorRank rank q = constructorRank rank r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h k ih ik => exact ih.trans ik
  case ordinary f g base target hf hg he ht hp =>
    exact congrArg some ((RankedPrecedenceChainsProof.actualHeadClassRank n table rank hrank f g).mp he)
  case numbered k f g tau base target types extras hf hg he hp =>
    exact congrArg some ((RankedPrecedenceChainsProof.actualHeadClassRank n table rank hrank f g).mp he)
  all_goals first | rfl | trivial

theorem primaryConstructorBaseCodes {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {Gamma : List Ty}
    {q r : Packed (Fin n) arity Gamma} (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    InUniverse symbols S q.2 →
      (constructorBaseCodes symbols S q).Perm (constructorBaseCodes symbols S r) := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl q => intro _; exact List.Perm.refl _
  case symm h ih =>
    intro hq
    exact (ih ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mpr hq)).symm
  case trans h k ih ik =>
    intro hq
    exact (ih hq).trans (ik ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mp hq))
  case ordinary f g base target hf hg he ht hp =>
    intro _
    exact hp.map (fun p => (p.1,representativeCode symbols S p))
  case numbered k f g tau base target types extras hf hg he hp =>
    intro _
    exact hp.map (fun p => (p.1,representativeCode symbols S p))
  case ordinaryArguments f base target h ih =>
    intro hq
    have he := argumentCodesPrimary hc h ⟨hq.1.2,hq.2.2⟩
    simp only [constructorBaseCodes,he]
    exact List.Perm.refl _
  case numberedBase k f tau base target types extras h ih =>
    intro hq
    have he := argumentCodesPrimary hc h ⟨hq.1.2.1,hq.2.2.1⟩
    simp only [constructorBaseCodes,he]
    exact List.Perm.refl _
  all_goals first | (intro _; exact List.Perm.refl _) | trivial

theorem primaryConstructorExtraCodes {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)}
    {S : List Ty} (hc : SubtypeClosed (fun t => t ∈ S)) {Gamma : List Ty}
    {q r : Packed (Fin n) arity Gamma} (h : WindowPrimary (Fin n) arity symbols S Gamma q r) :
    InUniverse symbols S q.2 → constructorExtraCodes symbols S q = constructorExtraCodes symbols S r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl q => intro _; rfl
  case symm h ih =>
    intro hq
    exact (ih ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mpr hq)).symm
  case trans h k ih ik =>
    intro hq
    exact (ih hq).trans (ik ((NumberedWindowEquivalenceProof.actualPrimaryConfinement (Fin n) arity symbols S _ _ _ h).mp hq))
  case numberedExtras k f tau base types extras target h ih =>
    intro hq
    exact argumentCodesPrimary hc h ⟨hq.1.2.2,hq.2.2.2⟩
  all_goals first | (intro _; rfl) | trivial
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorPrimaryMeasuresSupportProof
