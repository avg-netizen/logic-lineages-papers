module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExpansionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityOrdinaryStepProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceConstructorComputability SourceConstructorComputabilityMembersProof SourceConstructorComputabilityExpansionProof

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

/-- The ordinary induction premises indexed by an unrestricted packed source;
this avoids assuming injectivity of a head's result type during elimination. -/
def OrdinaryPremises (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (q : Packed (Fin n) arity Gamma) : Prop :=
  match q with
  | ⟨_,.ordinary f base⟩ =>
      InUniverse ctx.1.1 ctx.1.2 (.ordinary f base) ∧ ArgumentsC context ctx scalar base ∧
      (∀ k : Nat, InUniverse ctx.1.1 ctx.1.2 (.numbered k f (headResult f) base [] .nil) →
        TermC context ctx scalar (.numbered k f (headResult f) base [] .nil)) ∧
      (∀ target : AuxArguments (Fin n) arity Gamma (headArguments arity f),
        Descent arity Gamma ctx (ArgumentValues ctx target) (ArgumentValues ctx base) →
        InUniverse ctx.1.1 ctx.1.2 (.ordinary f target) → ArgumentsC context ctx scalar target →
        TermC context ctx scalar (.ordinary f target))
  | _ => False

theorem ordinaryStepGeneral
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {tau : Ty} {q r : AuxTerm (Fin n) arity Gamma tau}
    (hs : WindowStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma tau q r) :
    OrdinaryPremises context ctx scalar ⟨tau,q⟩ → TermC context ctx scalar r := by
  cases hs with
  | put k f base =>
    intro H
    exact H.2.2.1 k (NumberedWindowReductionProof.stepGood ctx.1.1 ctx.1.2 hclosed
      (above := NumberedCopyCertificate.tableAbove ctx.2) (.put k f base) H.1)
  | ordinaryArguments f base target hstep =>
    intro H
    have hbaseGood : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
        (HeadInWindow arity ctx.1.1 ctx.1.2) base := ⟨H.1.1.2,H.1.2.2⟩
    exact H.2.2.2 target (argumentStepDescent hbaseGood hstep)
      (NumberedWindowReductionProof.stepGood ctx.1.1 ctx.1.2 hclosed (.ordinaryArguments f base target hstep) H.1)
      (argumentStepComputable hc hclosed hcal hbaseGood hstep H.2.1)
  | bottom q hne =>
    intro H
    cases q with
    | ordinary f base =>
      exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Gamma context ctx scalar
        hc hclosed hcal _ H.1.1.1
    | var => cases H
    | lam => cases H
    | app => cases H
    | bottom => cases H
    | numbered => cases H
  | select => intro H; cases H
  | copy => intro H; cases H
  | mul => intro H; cases H
  | abs => intro H; cases H
  | numberedBase => intro H; cases H
  | numberedExtras => intro H; cases H
  | appFunction => intro H; cases H
  | lam => intro H; cases H
  | beta => intro H; cases H

theorem ordinaryStep
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (hg : InUniverse ctx.1.1 ctx.1.2 (.ordinary f base)) (hb : ArgumentsC context ctx scalar base)
    (hfinite : ∀ k : Nat, InUniverse ctx.1.1 ctx.1.2 (.numbered k f (headResult f) base [] .nil) →
      TermC context ctx scalar (.numbered k f (headResult f) base [] .nil))
    (hlowerBase : ∀ target : AuxArguments (Fin n) arity Gamma (headArguments arity f),
      Descent arity Gamma ctx (ArgumentValues ctx target) (ArgumentValues ctx base) →
      InUniverse ctx.1.1 ctx.1.2 (.ordinary f target) → ArgumentsC context ctx scalar target →
      TermC context ctx scalar (.ordinary f target)) :
    StepC context ctx scalar ⟨headResult f,.ordinary f base⟩ := by
  intro r hs
  exact ordinaryStepGeneral hc hclosed hcal hs ⟨hg,hb,hfinite,hlowerBase⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityOrdinaryStepProof
