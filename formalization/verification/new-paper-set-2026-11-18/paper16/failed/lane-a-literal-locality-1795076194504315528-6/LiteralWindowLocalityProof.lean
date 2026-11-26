import LogicLineages.PersistentMarking.LiteralWindowTermProof

namespace LogicLineages.PersistentMarking.LiteralWindowLocalityProof
open Spine LiteralDerivationTree LiteralDerivationLocalityTargets LiteralWindowSupportProof
open LiteralWindowTermProof

theorem locality : SymbolicLocality := by
  intro S K J tree hk
  induction tree with
  | var σ x =>
    intro h
    exact join (join h empty) empty
  | abs σ τ s t x hs ht hf hg child ih =>
    intro h
    have hsW : TermIn K (.lam σ s) := left h
    have htW : TermIn K (.lam σ t) := right h
    exact join (join h empty) (ih (join (opened hs hsW x) (opened ht htW x)))
  | funHead f g ss ts hs ht he hTy child ih =>
    intro h
    have hS : TermIn K (.head f ss) := left h
    have hT : TermIn K (.head g ts) := right h
    exact join (join h empty) (ih (join (right hS) (right hT)))
  | put f ss t hs ht child ih =>
    intro h
    have hS : TermIn K (.head f ss) := left h
    exact join (join h empty) (ih (join (markIn hS rfl) (right h)))
  | select f τ ss es t i q domains r hs ht ho hq hr child ih =>
    intro h
    have hOwn : TermIn K (.marked f τ ss es) := left h
    obtain ⟨hSel,hPrefix,hCopies,hResult⟩ := selectFacts hk hOwn hs.1 ho hq hr
    exact join (join h (join (join hSel hPrefix) hCopies)) (ih (join hResult (right h)))
  | fabs f σ τ ss es body x hs ht hf hg child ih =>
    intro h
    have hOwn : TermIn K (.marked f (.arrow σ τ) ss es) := left h
    have hT : TermIn K (.lam σ body) := right h
    exact join (join h empty) (ih (join (fabsSource x hOwn) (opened ht hT x)))
  | copy f g ss es ts hs ht hp child ih =>
    intro h
    have hOwn : TermIn K (.marked f g.result ss es) := left h
    have hT : TermIn K (.head g ts) := right h
    obtain ⟨hd,_,hb,he⟩ := markedParts hOwn
    exact join (join h empty) (ih (join (join (join hd hb) he) (right hT)))
  | stat f g ss es ts hs ht he multi whole ihM ihW =>
    intro h
    have hOwn : TermIn K (.marked f g.result ss es) := left h
    have hT : TermIn K (.head g ts) := right h
    obtain ⟨hd,_,hb,he⟩ := markedParts hOwn
    have hts := right hT
    exact join (join h empty)
      (join (ihM (join hb hts)) (ihW (join (join (join hd hb) he) hts)))
  | strictIntro q t r σ hq ht hm child ih =>
    intro h
    exact join (join h empty) (ih (join (markIn (left h) hm) (right h)))
  | matchingNil =>
    intro h
    exact join (join h empty) empty
  | matchingCons x y xs targets rest hr child more ihW ihM =>
    intro h
    have hx : TermIn K x := left (left h)
    have hxs : ArgsIn K xs := right (left h)
    obtain ⟨hy,ht⟩ := removeParts hr (right h)
    exact join (join h empty) (join (ihW (join hx hy)) (ihM (join hxs ht)))
  | multisetReplace source kept removed target matched added hs ht hn m c ihM ihC =>
    intro h
    obtain ⟨hk,hr⟩ := splitParts hs (left h)
    obtain ⟨hm,ha⟩ := splitParts ht (right h)
    exact join (join h empty) (join (ihM (join hk hm)) (ihC (join hr ha)))
  | coverageNil owners =>
    intro h
    exact join (join h empty) empty
  | coverageCons owners i q x xs hAt child more ihS ihC =>
    intro h
    have hOwners : ArgsIn K owners := left h
    have hq := selected hAt hOwners
    have hx : TermIn K x := left (right h)
    have hxs : ArgsIn K xs := right (right h)
    exact join (join h empty) (join (ihS (join hq hx)) (ihC (join hOwners hxs)))
  | wholeNil f bs es =>
    intro h
    exact join (join h empty) empty
  | wholeCons f q bs es qs child more ihW ihMore =>
    intro h
    have hd : Covers K (DecisionInventory.declaration f) := left (left (left h))
    have hb : ArgsIn K bs := right (left (left h))
    have he : ArgsIn K es := right (left h)
    have hq : TermIn K q := left (right h)
    have hqs : ArgsIn K qs := right (right h)
    have hOwn : TermIn K (.marked f q.type bs es) :=
      markedBuild hd (hk q.type (rootIn hq)) hb he
    exact join (join h empty) (join (ihW (join hOwn hq)) (ihMore (join (left h) hqs)))

end LogicLineages.PersistentMarking.LiteralWindowLocalityProof
