module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationFunctionalCasesProof

@[expose] public section
/-! The ACTUAL five-way original-derivation induction discharges every
constructor certificate premise. No conditional helper is promoted to a
closed theorem without this induction. Fixed-S quotient/coding/ID1 are NOT
consequences of the raw simulation proved here.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedDerivationCertificates

theorem weakCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : OriginalPacked Symbol arity Gamma}
    (h : RecursiveComparison.Weak Symbol arity above Gamma s t) : WeakCertificate above s t := by
  induction h using RecursiveComparison.Weak.rec
    (motive_2 := fun Gamma s t _ => StrictCertificate above s t)
    (motive_3 := fun Gamma ss ts _ => MatchCertificate above ss ts)
    (motive_4 := fun Gamma ss ts _ => MultiCertificate above ss ts)
    (motive_5 := fun Gamma ss ts _ => ReplacementCertificate above ss ts)
  case var v => exact NumberedDerivationWeakBasicCasesProof.varCase above v
  case abs s t hw ih => exact NumberedDerivationWeakBasicCasesProof.absCase s t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact NumberedDerivationWeakBasicCasesProof.funCase f g ss ts matched he ht hp ih
  case put f base t hw ih => exact NumberedDerivationWeakBasicCasesProof.putCase f base t ih
  case select f base types extras requested q r t suffix hm ha hw ih =>
    exact NumberedDerivationFunctionalCasesProof.selectCase f base types extras requested q r t suffix hm ha ih
  case fAbs f base types extras t hw ih => exact NumberedDerivationFunctionalCasesProof.fAbsCase f base types extras t ih
  case copy f g base types extras target hp hw ih => exact NumberedDerivationFunctionalCasesProof.copyCase f g base types extras target hp ih
  case stat f g base types extras target he hm hw ihm ihw => exact NumberedDerivationWeakBasicCasesProof.statCase f g base types extras target he ihm
  case mark s r t hm hw ih => exact NumberedDerivationListCasesProof.strictMarkCase s r t hm ih
  case nil => exact NumberedDerivationListCasesProof.matchNil above _
  case cons s t ss ts hw hm ihw ihm => exact NumberedDerivationListCasesProof.matchCons s t ss ts ihw ihm
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr =>
    exact NumberedDerivationListCasesProof.multisetReplace ss ts kept retained removed inserted hs ht hn ihw ihr
  case nil => intros; exact NumberedDerivationListCasesProof.replacementNil above _ _
  case cons =>
    intros
    rename_i Gamma removed s t rest hm hs hr ihs ihr
    exact NumberedDerivationListCasesProof.replacementCons removed s t rest hm ihs ihr

theorem strictCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : OriginalPacked Symbol arity Gamma}
    (h : RecursiveComparison.Strict Symbol arity above Gamma s t) : StrictCertificate above s t := by
  cases h with
  | mark s r t hm hw => exact NumberedDerivationListCasesProof.strictMarkCase s r t hm (weakCertificates above hw)

theorem matchCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts) : MatchCertificate above ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact NumberedDerivationListCasesProof.matchNil above Gamma
  | cons s ss ih => cases h with
    | cons s t ss ts hw hr => exact NumberedDerivationListCasesProof.matchCons s t ss ts (weakCertificates above hw) (ih hr)

theorem replacementCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.ReplacementMatch Symbol arity above Gamma ss ts) : ReplacementCertificate above ss ts := by
  induction ts generalizing ss with
  | nil => exact NumberedDerivationListCasesProof.replacementNil above Gamma ss
  | cons t ts ih => cases h with
    | cons removed s t rest hs hst hr => exact NumberedDerivationListCasesProof.replacementCons _ s t _ hs (strictCertificates above hst) (ih hr)

theorem multisetCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts) : MultiCertificate above ss ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hw hr =>
    exact NumberedDerivationListCasesProof.multisetReplace ss ts kept retained removed inserted hs ht hn
      (matchCertificates above hw) (replacementCertificates above hr)

theorem weakSimulation : NumberedDerivationSimulationTargets.ActualWeakSimulation := by
  intro Symbol arity above Gamma s t h
  exact weakCertificates above h

theorem strictInitialMark : NumberedDerivationSimulationTargets.ActualStrictInitialMark := by
  intro Symbol arity above Gamma s t h
  exact strictCertificates above h

theorem strictSimulation : NumberedDerivationSimulationTargets.ActualStrictSimulation := by
  intro Symbol arity above Gamma s t h
  cases h with
  | mark s r t hm hw =>
    obtain ⟨B,hB⟩ := weakCertificates above hw
    refine ⟨B+1,?_⟩
    intro Q hQ
    obtain ⟨R,hraw,hR⟩ := NumberedPositiveMarkProof.rawPositiveMark Symbol arity above B _ _ s r hm Q hQ
    obtain ⟨n,hn⟩ := hB R hR
    exact ⟨1+n,by omega,.trans (.raw _ _ hraw) hn⟩

theorem matchSimulation : NumberedDerivationSimulationTargets.ActualMatchSimulation := by
  intro Symbol arity above Gamma ss ts h
  exact matchCertificates above h

theorem multisetSimulation : NumberedDerivationSimulationTargets.ActualMultisetSimulation := by
  intro Symbol arity above Gamma ss ts h
  exact multisetCertificates above h

theorem replacementSimulation : NumberedDerivationSimulationTargets.ActualReplacementSimulation := by
  intro Symbol arity above Gamma ss ts h
  exact replacementCertificates above h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDerivationSimulationProof
