module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedDirectCertificate NumberedSelectCertificate NumberedMulCertificate NumberedStepContexts NumberedRootDecomposition

theorem rootErasure {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S : List Ty}
    {above : Fin n → Fin n → Prop} {Gamma : List Ty} {q r : Packed (Fin n) arity Gamma}
    (h : RootInstance n arity symbols S above Gamma q r) :
    ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),q=⟨tau,a⟩ ∧ r=⟨tau,b⟩ ∧ WindowStep (Fin n) arity symbols S above Gamma tau a b := by
  cases h with
  | direct rule q r h => cases h with
    | put label f base => exact ⟨_,_,_,rfl,rfl,.put label f base⟩
    | abstraction k f sigma tau base types extras => exact ⟨_,_,_,rfl,rfl,.abs k f base types extras⟩
    | beta sigma tau body a => exact ⟨_,_,_,rfl,rfl,.beta body a⟩
    | bottom tau q hn => exact ⟨_,_,_,rfl,rfl,.bottom q hn⟩
  | select q r h => cases h with
    | select k f tau base extraTypes extras types selected hm => exact ⟨_,_,_,rfl,rfl,.select k f base extraTypes extras types selected hm⟩
  | mul q r h => cases h with
    | mul k f g base types extras target he hw hm => exact ⟨_,_,_,rfl,rfl,.mul k f g base types extras target he hm hw⟩
  | copy k f g base types extras he hw => exact ⟨_,_,_,rfl,rfl,.copy k f g base types extras he hw⟩

theorem rootTyped {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S : List Ty}
    {above : Fin n → Fin n → Prop} {Gamma : List Ty} {tau : Ty} {q r : AuxTerm (Fin n) arity Gamma tau}
    (h : RootInstance n arity symbols S above Gamma ⟨tau,q⟩ ⟨tau,r⟩) : WindowStep (Fin n) arity symbols S above Gamma tau q r := by
  obtain ⟨upsilon,a,b,ha,hb,hs⟩ := rootErasure h
  cases ha
  cases hb
  exact hs

theorem decomposeTerm {n : Nat} {arity : Fin n → Nat} {symbols : List (Fin n)} {S : List Ty}
    {above : Fin n → Fin n → Prop} {Gamma : List Ty} {tau : Ty} {q r : AuxTerm (Fin n) arity Gamma tau}
    (h : WindowStep (Fin n) arity symbols S above Gamma tau q r) : TermDecomposition symbols S above q r := by
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types a b _ => ArgumentDecomposition symbols S above a b)
  case put k f base => exact ⟨_,_,_,_,.hole,rfl,rfl,.direct (.put k) _ _ (.put k f base)⟩
  case select k f base types extras ts selected hm => exact ⟨_,_,_,_,.hole,rfl,rfl,.select _ _ (.select k f _ base types extras ts selected hm)⟩
  case copy k f g base types extras he hw => exact ⟨_,_,_,_,.hole,rfl,rfl,.copy k f g base types extras he hw⟩
  case mul k f g base types extras target he hm hw => exact ⟨_,_,_,_,.hole,rfl,rfl,.mul _ _ (.mul k f g base types extras target he hw hm)⟩
  case abs k f base types extras => exact ⟨_,_,_,_,.hole,rfl,rfl,.direct .abstraction _ _ (.abstraction k f _ _ base types extras)⟩
  case ordinaryArguments f base target h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.ordinary f c,rfl,rfl,hr⟩
  case numberedBase k f tau base target types extras h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.numberedBase k f tau c types extras,rfl,rfl,hr⟩
  case numberedExtras k f tau base types extras target h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.numberedExtras k f tau base types c,rfl,rfl,hr⟩
  case appFunction q r arg h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.appFunction c arg,rfl,rfl,hr⟩
  case lam q r h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.lam c,rfl,rfl,hr⟩
  case beta body a => exact ⟨_,_,_,_,.hole,rfl,rfl,.direct .beta _ _ (.beta _ _ body a)⟩
  case bottom q hn => exact ⟨_,_,_,_,.hole,rfl,rfl,.direct .bottom _ _ (.bottom _ q hn)⟩
  case head q r rest h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.head c rest,rfl,rfl,hr⟩
  case tail q rest target h ih =>
    obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih
    exact ⟨HG,HT,a,b,.tail q c,rfl,rfl,hr⟩

theorem termRootDecomposition : NumberedRootDecompositionTargets.ActualTermRootDecomposition := by
  intro n arity symbols S above Gamma tau q r
  constructor
  · exact decomposeTerm
  · rintro ⟨HG,HT,a,b,c,rfl,rfl,hr⟩
    exact NumberedStepContextsProof.liftTerm symbols S above a b (rootTyped hr) c

theorem argumentRootDecomposition : NumberedRootDecompositionTargets.ActualArgumentRootDecomposition := by
  intro n arity symbols S above Gamma types q r
  constructor
  · intro h
    induction types with
    | nil => cases h
    | cons sigma types ih => cases h with
      | head q r rest hs =>
        obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := decomposeTerm hs
        exact ⟨HG,HT,a,b,.head c rest,rfl,rfl,hr⟩
      | tail q rest target hs =>
        obtain ⟨HG,HT,a,b,c,rfl,rfl,hr⟩ := ih rest target hs
        exact ⟨HG,HT,a,b,.tail q c,rfl,rfl,hr⟩
  · rintro ⟨HG,HT,a,b,c,rfl,rfl,hr⟩
    exact NumberedStepContextsProof.liftArguments symbols S above a b (rootTyped hr) c

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionProof
