module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawWitnessLaws
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimitiveWitnessChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowHeadEnumerationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootBuild
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessRootBits NumberedWindowRawWitnessBits NumberedWindowRawWitnessLaws
open NumberedWindowHeadEnumerationTargets (headBit)

def TermCert (S : Signature) (K : List Ty) (Q R : NTerm) : Prop :=
  ∃ w, rawBit S K w Q R = true

def ArgsCert (S : Signature) (K : List Ty) (qs rs : NArgs) : Prop :=
  ∃ i w, argsAtBit (rawBit S K w) i qs rs = true

private theorem viaRoot {S K w Q R} (h : rootBit S K w Q R = true) : TermCert S K Q R :=
  ⟨.root w,h⟩

theorem mark {S K f bs k} :
    TermCert S K (.ordinary f bs) (.numbered f f.result k bs .nil) :=
  viaRoot (w := .mark k) (termRefl _)

theorem lower {S K f τ k bs es} :
    TermCert S K (.numbered f τ (k+1) bs es) (.numbered f τ k bs es) :=
  viaRoot (w := .lower) (termRefl _)

private theorem selectSide {S K f τ k bs es a} {ex : Bool} {i domains R}
    (hg : (if ex then es else bs : NArgs).get i = some a)
    (ht : a.type = ArrowPrefix domains τ)
    (ha : applications a (ownerCopies f k bs es domains) = some R) :
    TermCert S K (.numbered f τ (k+1) bs es) R := by
  apply viaRoot (w := .select ex i domains)
  change rootBit S K (.select ex i domains) (.numbered f τ (.succ k) bs es) R = true
  simp only [rootBit,hg,Bool.and_eq_true,decide_eq_true_eq,resultTrue]
  exact ⟨ht,ha⟩

theorem select {S K f τ k bs es a i domains R}
    (hg : bs.get i = some a ∨ es.get i = some a)
    (ht : a.type = ArrowPrefix domains τ)
    (ha : applications a (ownerCopies f k bs es domains) = some R) :
    TermCert S K (.numbered f τ (k+1) bs es) R := by
  rcases hg with hg | hg
  · exact selectSide (ex := false) hg ht ha
  · exact selectSide (ex := true) hg ht ha

theorem copy {S K f g k bs es} (hp : Precedes S f g) (hg : HeadInWindow S K g) :
    TermCert S K (.numbered f g.result (k+1) bs es)
      (.ordinary g (ownerCopies f k bs es g.arguments)) := by
  apply viaRoot (w := .copy)
  change rootBit S K .copy (.numbered f g.result (.succ k) bs es)
    (.ordinary g (ownerCopies f k bs es g.arguments)) = true
  simp [rootBit,(precedes S f g).mpr hp,
    (NumberedWindowHeadEnumerationProof.bit S K g).mpr hg,argsRefl]

theorem stat {S K f g k bs es target} (he : Equivalent S f g)
    (hg : HeadInWindow S K g) (hp : PrimitiveReplacement bs target) :
    TermCert S K (.numbered f g.result (k+1) bs es) (.ordinary g target) := by
  obtain ⟨part,hpart⟩ :=
    (NumberedWindowPrimitiveWitnessChecks.exact_CertifiedPrimitiveReplacement bs target).mpr hp
  apply viaRoot (w := .stat part)
  change rootBit S K (.stat part) (.numbered f g.result (.succ k) bs es)
    (.ordinary g target) = true
  simp [rootBit,(equivalent S f g).mpr he,(NumberedWindowHeadEnumerationProof.bit S K g).mpr hg,
    hpart]

theorem fabs {S K f σ τ k bs es} :
    TermCert S K (.numbered f (.arrow σ τ) (k+1) bs es)
      (.lam σ (openNumbered f σ τ k bs es)) :=
  viaRoot (w := .fabs) (termRefl _)

theorem beta {S K σ τ body a} :
    TermCert S K (.auxApp σ τ (.lam σ body) a) (substitute (.cons a .nil) 0 body) := by
  apply viaRoot (w := .beta)
  simp [rootBit,termRefl]

theorem bottom {S K Q} (hn : Q ≠ .bottom Q.type) :
    TermCert S K Q (.bottom Q.type) := by
  have e : termEq Q (.bottom Q.type) = false :=
    Bool.eq_false_iff.mpr (fun h => hn ((termEqTrue _ _).mp h))
  apply viaRoot (w := .bottom)
  simp [rootBit,e,termRefl]

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootBuild
