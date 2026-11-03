module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationTargets

@[expose] public section
/-! The ACTUAL five-way original-derivation induction discharges every
constructor certificate premise. No conditional helper is promoted to a
closed theorem without this induction. Fixed-S quotient/coding/ID1 are NOT
consequences of this restricted simulation with explicit confinement.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedOccurrenceTransport NumberedDerivationSimulation NumberedWindowCertificates NumberedFiniteUniverse NumberedWindowTraces

theorem weakCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (hc : SubtypeClosed (fun t => t∈S)) {s t : OriginalPacked Symbol arity Gamma}
    (h : RecursiveComparison.Weak Symbol arity above Gamma s t) : WeakCertificate symbols S above s t := by
  induction h using RecursiveComparison.Weak.rec
    (motive_2 := fun Gamma s t _ => StrictCertificate symbols S above s t)
    (motive_3 := fun Gamma ss ts _ => MatchCertificate symbols S above ss ts)
    (motive_4 := fun Gamma ss ts _ => MultiCertificate symbols S above ss ts)
    (motive_5 := fun Gamma ss ts _ => ReplacementCertificate symbols S above ss ts)
  case var v => exact NumberedWindowBasicCasesProof.varCase Symbol arity symbols S above _ _ v
  case abs s t hw ih => exact NumberedWindowBasicCasesProof.absCase Symbol arity symbols S above _ _ _ s t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact NumberedWindowBasicCasesProof.funCase Symbol arity symbols S above _ f g ss ts matched he ht hp ih
  case put f base t hw ih => exact NumberedWindowBasicCasesProof.putCase Symbol arity symbols S above _ f base t ih
  case select f base types extras requested q r t suffix hm ha hw ih =>
    exact NumberedWindowFunctionalCasesProof.selectCase Symbol arity symbols S above hc _ _ _ f base types extras requested q r t suffix hm ha ih
  case fAbs f base types extras t hw ih => exact NumberedWindowFunctionalCasesProof.fAbsCase Symbol arity symbols S above hc _ _ _ f base types extras t ih
  case copy f g base types extras target hp hw ih => exact NumberedWindowFunctionalCasesProof.copyCase Symbol arity symbols S above _ f g base types extras target hp ih
  case stat f g base types extras target he hm hw ihm ihw => exact NumberedWindowBasicCasesProof.statCase Symbol arity symbols S above _ f g base types extras target he ihm
  case mark s r t hm hw ih => exact NumberedWindowListCasesProof.strictMarkCase Symbol arity symbols S above _ _ s r t hm ih
  case nil => exact NumberedWindowListCasesProof.matchNil Symbol arity symbols S above _
  case cons s t ss ts hw hm ihw ihm => exact NumberedWindowListCasesProof.matchCons Symbol arity symbols S above _ s t ss ts ihw ihm
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr =>
    exact NumberedWindowListCasesProof.multisetReplace Symbol arity symbols S above _ ss ts kept retained removed inserted hs ht hn ihw ihr
  case nil => intros; exact NumberedWindowListCasesProof.replacementNil Symbol arity symbols S above _ _
  case cons =>
    intros
    rename_i Gamma removed s t rest hm hs hr ihs ihr
    exact NumberedWindowListCasesProof.replacementCons Symbol arity symbols S above _ removed s t rest hm ihs ihr

theorem strictCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (hc : SubtypeClosed (fun t => t∈S)) {s t : OriginalPacked Symbol arity Gamma}
    (h : RecursiveComparison.Strict Symbol arity above Gamma s t) : StrictCertificate symbols S above s t := by
  cases h with
  | mark s r t hm hw => exact NumberedWindowListCasesProof.strictMarkCase Symbol arity symbols S above _ _ s r t hm (weakCertificates symbols S above hc hw)

theorem matchCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (hc : SubtypeClosed (fun t => t∈S)) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.WeakMatch Symbol arity above Gamma ss ts) : MatchCertificate symbols S above ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact NumberedWindowListCasesProof.matchNil Symbol arity symbols S above Gamma
  | cons s ss ih => cases h with
    | cons s t ss ts hw hr => exact NumberedWindowListCasesProof.matchCons Symbol arity symbols S above _ s t ss ts (weakCertificates symbols S above hc hw) (ih hr)

theorem replacementCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (hc : SubtypeClosed (fun t => t∈S)) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.ReplacementMatch Symbol arity above Gamma ss ts) : ReplacementCertificate symbols S above ss ts := by
  induction ts generalizing ss with
  | nil => exact NumberedWindowListCasesProof.replacementNil Symbol arity symbols S above Gamma ss
  | cons t ts ih => cases h with
    | cons removed s t rest hs hst hr => exact NumberedWindowListCasesProof.replacementCons Symbol arity symbols S above _ _ s t _ hs (strictCertificates symbols S above hc hst) (ih hr)

theorem multisetCertificates {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop) (hc : SubtypeClosed (fun t => t∈S)) {ss ts : List (OriginalPacked Symbol arity Gamma)}
    (h : RecursiveComparison.StrictMultiset Symbol arity above Gamma ss ts) : MultiCertificate symbols S above ss ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hw hr =>
    exact NumberedWindowListCasesProof.multisetReplace Symbol arity symbols S above _ ss ts kept retained removed inserted hs ht hn
      (matchCertificates symbols S above hc hw) (replacementCertificates symbols S above hc hr)

theorem weakSimulation : NumberedWindowSimulationTargets.ActualWeakSimulation := by
  intro Symbol arity symbols S above hc Gamma s t h
  exact weakCertificates symbols S above hc h

theorem strictInitialMark : NumberedWindowSimulationTargets.ActualStrictInitialMark := by
  intro Symbol arity symbols S above hc Gamma s t h
  exact strictCertificates symbols S above hc h

theorem strictSimulation : NumberedWindowSimulationTargets.ActualStrictSimulation := by
  intro Symbol arity symbols S above hc Gamma s t h
  cases h with
  | mark s r t hm hw =>
    obtain ⟨B,hB⟩ := weakCertificates symbols S above hc hw
    refine ⟨B+1,?_⟩
    intro Q hQ hgood htarget
    obtain ⟨R,hraw,hR⟩ := NumberedWindowOccurrenceProof.originalPositiveMark Symbol arity symbols S above B _ _ s r hm Q hQ
    have hRgood := NumberedWindowReductionProof.stepGood symbols S hc hraw hgood
    obtain ⟨n,hn⟩ := hB R hR hRgood htarget
    exact ⟨1+n,by omega,.trans (.raw _ _ hraw) hn⟩

theorem matchSimulation : NumberedWindowSimulationTargets.ActualMatchSimulation := by
  intro Symbol arity symbols S above hc Gamma ss ts h
  exact matchCertificates symbols S above hc h

theorem multisetSimulation : NumberedWindowSimulationTargets.ActualMultisetSimulation := by
  intro Symbol arity symbols S above hc Gamma ss ts h
  exact multisetCertificates symbols S above hc h

theorem replacementSimulation : NumberedWindowSimulationTargets.ActualReplacementSimulation := by
  intro Symbol arity symbols S above hc Gamma ss ts h
  exact replacementCertificates symbols S above hc h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowSimulationProof
