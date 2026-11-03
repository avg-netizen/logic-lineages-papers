module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseBindingProof NumberedUniverseOperationsTargets NumberedUniverseOperationsProof NumberedWindowReduction NumberedWindowReductionTargets

theorem actualStepErasure : ActualStepErasure := by
  intro Symbol arity symbols S above Gamma tau q r h
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types a b _ => ArgumentStep Symbol arity above Gamma types a b)
  case put n f base => exact .put n f base
  case select n f base types extras ts selected hm => exact .select n f base types extras ts selected hm
  case copy n f g base types extras hg hw => exact .copy n f g base types extras hg
  case mul n f g base types extras target hg hm hw => exact .mul n f g base types extras target hg hm
  case abs n f base types extras => exact .abs n f base types extras
  case ordinaryArguments f base target h ih => exact .ordinaryArguments f base target ih
  case numberedBase n f tau base target types extras h ih => exact .numberedBase n f tau base target types extras ih
  case numberedExtras n f tau base types extras target h ih => exact .numberedExtras n f tau base types extras target ih
  case appFunction q r a h ih => exact .appFunction q r a ih
  case lam q r h ih => exact .lam q r ih
  case beta body a => exact .beta body a
  case bottom q h => exact .bottom q h
  case head => exact .head _ _ _ ‹RawStep _ _ _ _ _ _ _›
  case tail => exact .tail _ _ _ ‹ArgumentStep _ _ _ _ _ _ _›

theorem actualArgumentErasure : ActualArgumentErasure := by
  intro Symbol arity symbols S above Gamma types a b h
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest h => exact .head q r rest (actualStepErasure Symbol arity symbols S above _ _ q r h)
    | tail q rest target h => exact .tail q rest target (ih rest target h)

theorem stepGood {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (hc : SubtypeClosed (fun t => t∈S)) {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {q r : AuxTerm Symbol arity Gamma tau} (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    InUniverse symbols S q → InUniverse symbols S r := by
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types a b _ => GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a →
      GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) b)
  case put n f base =>
    intro hg
    exact ⟨⟨hg.1.1,hg.1.2,trivial⟩,hg.2.1,hg.2.2,trivial⟩
  case select n f base types extras ts selected hm =>
    intro hg
    exact actualSelect Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) hc n _ f _ base types extras ts selected hm hg
  case copy n f g base types extras hg hw =>
    intro hq
    have hb : GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) base := ⟨hq.1.2.1,hq.2.2.1⟩
    have he : GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) extras := ⟨hq.1.2.2,hq.2.2.2⟩
    have hs := actualSelfArguments Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S)
      n _ f base types extras (headArguments arity g) hq.2.1 hb he hw.2.2
    exact ⟨⟨hq.1.1,hs.1⟩,hw,hs.2⟩
  case mul n f g base types extras target hg hm hw =>
    intro hq
    have hb : GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) base := ⟨hq.1.2.1,hq.2.2.1⟩
    have hl := (actualArgumentOccurrences Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) _ _ base).mp hb
    have ht := (actualArgumentOccurrences Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) _ _ target).mpr
      (actualPrimitiveMultiset Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) _ _ _ hm hl)
    exact ⟨⟨hq.1.1,ht.1⟩,hw,ht.2⟩
  case abs n f base types extras =>
    intro hq
    have hb := actualOpenedNumbered Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S)
      hc n (n+1) _ f _ _ base types extras hq
    have hs := arrowDomain (fun t => t∈S) hc _ _ hq.1.1
    exact ⟨⟨hq.1.1,hs,hb.1⟩,hb.2⟩
  case ordinaryArguments f base target h ih =>
    intro hq
    have ht := ih ⟨hq.1.2,hq.2.2⟩
    exact ⟨⟨hq.1.1,ht.1⟩,hq.2.1,ht.2⟩
  case numberedBase n f tau base target types extras h ih =>
    intro hq
    have ht := ih ⟨hq.1.2.1,hq.2.2.1⟩
    exact ⟨⟨hq.1.1,ht.1,hq.1.2.2⟩,hq.2.1,ht.2,hq.2.2.2⟩
  case numberedExtras n f tau base types extras target h ih =>
    intro hq
    have ht := ih ⟨hq.1.2.2,hq.2.2.2⟩
    exact ⟨⟨hq.1.1,hq.1.2.1,ht.1⟩,hq.2.1,hq.2.2.1,ht.2⟩
  case appFunction q r a h ih =>
    intro hq
    have hr := ih ⟨hq.1.2.1,hq.2.1⟩
    exact ⟨⟨hq.1.1,hr.1,hq.1.2.2⟩,hr.2,hq.2.2⟩
  case lam q r h ih =>
    intro hq
    have hr := ih ⟨hq.1.2.2,hq.2⟩
    exact ⟨⟨hq.1.1,hq.1.2.1,hr.1⟩,hr.2⟩
  case beta body a =>
    intro hq
    exact actualBeta Symbol arity (fun t => t∈S) (HeadInWindow arity symbols S) _ _ _ body a
      ⟨hq.1.2.1.2.2,hq.2.1⟩ ⟨hq.1.2.2,hq.2.2⟩
  case bottom q hn =>
    intro hq
    exact ⟨rootType (fun t => t∈S) (HeadInWindow arity symbols S) q hq,trivial⟩
  case head Gamma sigma types q r rest h ih hg =>
    have hr := ih ⟨hg.1.1,hg.2.1⟩
    exact ⟨⟨hr.1,hg.1.2⟩,hr.2,hg.2.2⟩
  case tail Gamma sigma types q rest target h ih hg =>
    have hr := ih ⟨hg.1.2,hg.2.2⟩
    exact ⟨⟨hg.1.1,hr.1⟩,hg.2.1,hr.2⟩

theorem actualStepConfinement : ActualStepConfinement := by
  intro Symbol arity symbols S hc above Gamma tau q r h hg
  exact stepGood symbols S hc h hg

theorem actualArgumentConfinement : ActualArgumentConfinement := by
  intro Symbol arity symbols S hc above Gamma types a b h hg
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest h =>
      have hr := stepGood symbols S hc h ⟨hg.1.1,hg.2.1⟩
      exact ⟨⟨hr.1,hg.1.2⟩,hr.2,hg.2.2⟩
    | tail q rest target h =>
      have hr := ih rest target h ⟨hg.1.2,hg.2.2⟩
      exact ⟨⟨hg.1.1,hr.1⟩,hg.2.1,hr.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionProof
