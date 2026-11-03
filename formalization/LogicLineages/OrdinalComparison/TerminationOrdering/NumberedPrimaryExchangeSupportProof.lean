module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeSupportProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryExchange

theorem argsRefl {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) : WindowArgumentPrimary Symbol arity symbols S Gamma types args args := by
  induction types with
  | nil => cases args; exact .nil
  | cons sigma types ih => cases args with
    | cons q rest => exact .cons q q rest rest (.refl _) (ih rest)

theorem argsTrans {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma types : List Ty}
    {a b c : AuxArguments Symbol arity Gamma types}
    (hab : WindowArgumentPrimary Symbol arity symbols S Gamma types a b)
    (hbc : WindowArgumentPrimary Symbol arity symbols S Gamma types b c) :
    WindowArgumentPrimary Symbol arity symbols S Gamma types a c := by
  induction types with
  | nil => cases hab; cases hbc; exact .nil
  | cons sigma types ih => cases hab with
    | cons q r rest target hq hr => cases hbc with
      | cons _ s _ last hs ht => exact .cons q s rest last (.trans hq hs) (ih hr ht)

theorem erase {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : Exchange Symbol arity symbols S Gamma q r) :
    WindowPrimary Symbol arity symbols S Gamma q r := by
  induction h using Exchange.rec
    (motive_2 := fun Gamma types a b _ => WindowArgumentPrimary Symbol arity symbols S Gamma types a b)
  case ordinary f g base target hf hg he ht hp => exact .ordinary f g base target hf hg he ht hp
  case numbered k f g tau base target types extras hf hg he hp => exact .numbered k f g tau base target types extras hf hg he hp
  case lam q r h ih => exact .lam q r ih
  case appFunction q r a h ih => exact .appFunction q r a ih
  case appArgument q a b h ih => exact .appArgument q a b ih
  case ordinaryArguments f base target h ih => exact .ordinaryArguments f base target ih
  case numberedBase k f tau base target types extras h ih => exact .numberedBase k f tau base target types extras ih
  case numberedExtras k f tau base types extras target h ih => exact .numberedExtras k f tau base types extras target ih
  case head q r rest h ih => exact .cons q r rest rest ih (argsRefl rest)
  case tail q rest target h ih => exact .cons q q rest target (.refl _) ih

theorem argsErase {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma types : List Ty}
    {a b : AuxArguments Symbol arity Gamma types} (h : ArgumentExchange Symbol arity symbols S Gamma types a b) :
    WindowArgumentPrimary Symbol arity symbols S Gamma types a b := by
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest h => exact .cons q r rest rest (erase h) (argsRefl rest)
    | tail q rest target h => exact .cons q q rest target (.refl _) (ih h)

theorem symmetry {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : Exchange Symbol arity symbols S Gamma q r) :
    Exchange Symbol arity symbols S Gamma r q := by
  induction h using Exchange.rec
    (motive_2 := fun Gamma types a b _ => ArgumentExchange Symbol arity symbols S Gamma types b a)
  case ordinary f g base target hf hg he ht hp => exact .ordinary g f target base hg hf (Eq.symm he) ht.symm hp.symm
  case numbered k f g tau base target types extras hf hg he hp => exact .numbered k g f tau target base types extras hg hf (Eq.symm he) hp.symm
  case lam q r h ih => exact .lam r q ih
  case appFunction q r a h ih => exact .appFunction r q a ih
  case appArgument q a b h ih => exact .appArgument q b a ih
  case ordinaryArguments f base target h ih => exact .ordinaryArguments f target base ih
  case numberedBase k f tau base target types extras h ih => exact .numberedBase k f tau target base types extras ih
  case numberedExtras k f tau base types extras target h ih => exact .numberedExtras k f tau base types target extras ih
  case head q r rest h ih => exact .head r q rest ih
  case tail q rest target h ih => exact .tail q target rest ih

theorem chainMap {alpha beta : Type} {R : alpha → alpha → Prop} {T : beta → beta → Prop}
    (f : alpha → beta) (hf : ∀ a b,R a b → T (f a) (f b)) {a b : alpha} (h : Chain R a b) : Chain T (f a) (f b) := by
  induction h with
  | refl a => exact .refl _
  | step h => exact .step (hf _ _ h)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem chainSymm {alpha : Type} {R : alpha → alpha → Prop}
    (hs : ∀ a b,R a b → R b a) {a b : alpha} (h : Chain R a b) : Chain R b a := by
  induction h with
  | refl => exact .refl _
  | step h => exact .step (hs _ _ h)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem chainLift {alpha beta : Type} {R : alpha → alpha → Prop} {T : beta → beta → Prop}
    (f : beta → alpha) (hs : ∀ b a,R (f b) a → ∃ c,f c=a ∧ T b c)
    {a a' : alpha} (h : Chain R a a') : ∀ b,f b=a → ∃ c,f c=a' ∧ Chain T b c := by
  induction h with
  | refl a => intro b hb; exact ⟨b,hb,.refl b⟩
  | step h =>
    intro b hb
    rw [← hb] at h
    obtain ⟨c,hc,ht⟩ := hs b _ h
    exact ⟨c,hc,.step ht⟩
  | trans h1 h2 ih1 ih2 =>
    intro b hb
    obtain ⟨c,hc,hbc⟩ := ih1 b hb
    obtain ⟨d,hd,hcd⟩ := ih2 c hc
    exact ⟨d,hd,.trans hbc hcd⟩

theorem typedChain {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty} {tau : Ty}
    {q r : AuxTerm Symbol arity Gamma tau}
    (h : Chain (Exchange Symbol arity symbols S Gamma) ⟨tau,q⟩ ⟨tau,r⟩) :
    Chain (fun a b : AuxTerm Symbol arity Gamma tau => Exchange Symbol arity symbols S Gamma ⟨tau,a⟩ ⟨tau,b⟩) q r := by
  have hs : ∀ (b : AuxTerm Symbol arity Gamma tau) (a : Packed Symbol arity Gamma),
      Exchange Symbol arity symbols S Gamma ⟨tau,b⟩ a →
      ∃ c : AuxTerm Symbol arity Gamma tau,(⟨tau,c⟩ : Packed Symbol arity Gamma)=a ∧ Exchange Symbol arity symbols S Gamma ⟨tau,b⟩ ⟨tau,c⟩ := by
    intro b a he
    have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation Symbol arity Gamma _ _
      (NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S Gamma _ _ (erase he))
    obtain ⟨upsilon,a⟩ := a
    change tau=upsilon at ht
    cases ht
    exact ⟨a,rfl,he⟩
  obtain ⟨c,hc,hpath⟩ := chainLift (fun a : AuxTerm Symbol arity Gamma tau => (⟨tau,a⟩ : Packed Symbol arity Gamma)) hs h q rfl
  have he : c=r := eq_of_heq (Sigma.mk.inj hc).2
  cases he
  exact hpath

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeSupportProof
