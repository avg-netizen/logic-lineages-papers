module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryExchange NumberedPrimaryExchangeSupportProof

theorem exchangeErasure : NumberedPrimaryExchangeTargets.ActualExchangeErasure := by
  intro Symbol arity symbols S Gamma q r h; exact erase h

theorem exchangeSymmetry : NumberedPrimaryExchangeTargets.ActualExchangeSymmetry := by
  intro Symbol arity symbols S Gamma q r h; exact symmetry h

theorem closureToPrimary {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : Chain (Exchange Symbol arity symbols S Gamma) q r) :
    WindowPrimary Symbol arity symbols S Gamma q r := by
  induction h with
  | refl => exact .refl _
  | step h => exact erase h
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem primaryToClosure {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    Chain (Exchange Symbol arity symbols S Gamma) q r := by
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types a b _ => Chain (ArgumentExchange Symbol arity symbols S Gamma types) a b)
  case refl q => exact .refl q
  case symm h ih => exact chainSymm (fun _ _ => symmetry) ih
  case trans h1 h2 ih1 ih2 => exact .trans ih1 ih2
  case ordinary f g base target hf hg he ht hp => exact .step (.ordinary f g base target hf hg he ht hp)
  case numbered k f g tau base target types extras hf hg he hp => exact .step (.numbered k f g tau base target types extras hf hg he hp)
  case lam Gamma sigma tau q r h ih =>
    exact chainMap (fun a => (⟨.arrow sigma tau,AuxTerm.lam a⟩ : Packed Symbol arity Gamma))
      (fun a b hab => Exchange.lam a b hab) (typedChain ih)
  case appFunction Gamma sigma tau q r a h ih =>
    exact chainMap (fun f => (⟨tau,AuxTerm.app f a⟩ : Packed Symbol arity Gamma))
      (fun f g hfg => Exchange.appFunction f g a hfg) (typedChain ih)
  case appArgument Gamma sigma tau q a b h ih =>
    exact chainMap (fun a => (⟨tau,AuxTerm.app q a⟩ : Packed Symbol arity Gamma))
      (fun a b hab => Exchange.appArgument q a b hab) (typedChain ih)
  case ordinaryArguments Gamma f base target h ih =>
    exact chainMap (fun a => (⟨headResult f,AuxTerm.ordinary f a⟩ : Packed Symbol arity Gamma))
      (fun a b hab => Exchange.ordinaryArguments f a b hab) ih
  case numberedBase Gamma k f tau base target types extras h ih =>
    exact chainMap (fun a => (⟨tau,AuxTerm.numbered k f tau a types extras⟩ : Packed Symbol arity Gamma))
      (fun a b hab => Exchange.numberedBase k f tau a b types extras hab) ih
  case numberedExtras Gamma k f tau base types extras target h ih =>
    exact chainMap (fun e => (⟨tau,AuxTerm.numbered k f tau base types e⟩ : Packed Symbol arity Gamma))
      (fun a b hab => Exchange.numberedExtras k f tau base types a b hab) ih
  case nil => exact .refl _
  case cons Gamma sigma types q r rest target hq ht ihq iht =>
    exact .trans
      (chainMap (fun a => AuxArguments.cons a rest) (fun a b hab => ArgumentExchange.head a b rest hab) (typedChain ihq))
      (chainMap (fun xs => AuxArguments.cons r xs) (fun xs ys hxy => ArgumentExchange.tail r xs ys hxy) iht)

theorem primaryClosure : NumberedPrimaryExchangeTargets.ActualPrimaryClosure := by
  intro Symbol arity symbols S Gamma q r
  exact ⟨closureToPrimary,primaryToClosure⟩

theorem argumentClosure : NumberedPrimaryExchangeTargets.ActualArgumentClosure := by
  intro Symbol arity symbols S Gamma types args target
  constructor
  · intro h
    induction h with
    | refl a => exact argsRefl a
    | step h => exact argsErase h
    | trans _ _ ih1 ih2 => exact argsTrans ih1 ih2
  · intro h
    induction types with
    | nil => cases h; exact .refl _
    | cons sigma types ih => cases h with
      | cons q r rest target hq ht =>
        exact .trans
          (chainMap (fun a => AuxArguments.cons a rest) (fun a b hab => ArgumentExchange.head a b rest hab) (typedChain (primaryToClosure hq)))
          (chainMap (fun xs => AuxArguments.cons r xs) (fun xs ys hxy => ArgumentExchange.tail r xs ys hxy) (ih rest target ht))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeProof
