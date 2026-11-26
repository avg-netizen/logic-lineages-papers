module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExpansionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySuccessorStepProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityApplicationProof SourceConstructorComputabilityExpansionProof
open RankedPrecedenceCertificate

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

/-- The seven genuine numbered successor cases, using only the earlier
coordinates of the lexicographic induction. -/
theorem numberedSuccessorStep
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (k : Nat) (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
    (hg : InUniverse ctx.1.1 ctx.1.2 (.numbered (k+1) f tau base types extras))
    (hb : ArgumentsC context ctx scalar base) (he : ArgumentsC context ctx scalar extras)
    (hlowerHead : ∀ (g : Head (Fin n)) (args : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
      headRank rank g < headRank rank f → InUniverse ctx.1.1 ctx.1.2 (.ordinary g args) →
      ArgumentsC context ctx scalar args → TermC context ctx scalar (.ordinary g args))
    (hlowerBaseOrd : ∀ (g : Head (Fin n)) (args : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
      headRank rank g = headRank rank f → Descent arity Gamma ctx (ArgumentValues ctx args) (ArgumentValues ctx base) →
      InUniverse ctx.1.1 ctx.1.2 (.ordinary g args) → ArgumentsC context ctx scalar args →
      TermC context ctx scalar (.ordinary g args))
    (hlowerBaseNum : ∀ (args : AuxArguments (Fin n) arity Gamma (headArguments arity f)),
      Descent arity Gamma ctx (ArgumentValues ctx args) (ArgumentValues ctx base) →
      InUniverse ctx.1.1 ctx.1.2 (.numbered (k+1) f tau args types extras) →
      ArgumentsC context ctx scalar args → TermC context ctx scalar (.numbered (k+1) f tau args types extras))
    (hlowerLabel : ∀ (upsilon : Ty) (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      InUniverse ctx.1.1 ctx.1.2 (.numbered k f upsilon base types' extras') →
      ArgumentsC context ctx scalar extras' → TermC context ctx scalar (.numbered k f upsilon base types' extras'))
    (hlowerExtra : ∀ (extras' : AuxArguments (Fin n) arity Gamma types),
      Descent arity Gamma ctx (ArgumentValues ctx extras') (ArgumentValues ctx extras) →
      InUniverse ctx.1.1 ctx.1.2 (.numbered (k+1) f tau base types extras') →
      ArgumentsC context ctx scalar extras' → TermC context ctx scalar (.numbered (k+1) f tau base types extras')) :
    StepC context ctx scalar ⟨tau,.numbered (k+1) f tau base types extras⟩ := by
  intro r hs
  have htarget := NumberedWindowReductionProof.stepGood ctx.1.1 ctx.1.2 hclosed hs hg
  have hbaseGood : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) base := ⟨hg.1.2.1,hg.2.2.1⟩
  have hextraGood : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) extras := ⟨hg.1.2.2,hg.2.2.2⟩
  have hself : ∀ selfTypes : List Ty, (∀ upsilon ∈ selfTypes, upsilon ∈ ctx.1.2) →
      ArgumentsC context ctx scalar (selfArguments k f base types extras selfTypes) := by
    intro selfTypes ht
    apply selfArgumentsComputable
    intro upsilon hu
    exact hlowerLabel upsilon types extras ⟨⟨ht upsilon hu,hbaseGood.1,hextraGood.1⟩,
      hg.2.1,hbaseGood.2,hextraGood.2⟩ he
  cases hs with
  | select k f base types extras selfTypes selected hselected =>
    have hselectedGood : InUniverse ctx.1.1 ctx.1.2 selected := by
      rcases List.mem_append.mp hselected with h | h
      · exact argumentsGood base hbaseGood _ h
      · exact argumentsGood extras hextraGood _ h
    have hselectedC : TermC context ctx scalar selected := by
      rcases List.mem_append.mp hselected with h | h
      · exact (argumentsC_iff base).mp hb _ h
      · exact (argumentsC_iff extras).mp he _ h
    have htypes := NumberedUniverseOperationsProof.arrowArgumentTypes (fun t => t ∈ ctx.1.2)
      hclosed selfTypes _ (NumberedUniverseOperationsProof.rootType _ _ selected hselectedGood)
    exact completeApplicationComputable hc hclosed selfTypes _ selected _ hselectedGood
      (NumberedUniverseBindingProof.actualSelfArguments (Fin n) arity _ _ k Gamma f base types extras
        selfTypes hg.2.1 hbaseGood hextraGood htypes)
      hselectedC (hself selfTypes htypes)
  | copy k f g base types extras habove hwindow =>
    exact hlowerHead g _
      ((RankedPrecedenceCertificateProof.actualHeadRankCalibration n ctx.2 rank hrank f g).mp habove)
      htarget (hself (headArguments arity g) hwindow.2.2)
  | mul k f g base types extras target hequiv hmulti hwindow =>
    apply hlowerBaseOrd g target
      ((RankedPrecedenceChainsProof.actualHeadClassRank n ctx.2 rank hrank f g).mp hequiv).symm
      (primitiveMultisetDescent hbaseGood hmulti) htarget
    exact (argumentsC_iff target).mpr
      (primitiveMultisetComputable hc hclosed hcal (argumentsGood base hbaseGood)
        ((argumentsC_iff base).mp hb) hmulti)
  | abs k f base types extras =>
    exact openedComputable hc hclosed hcal k f _ _ base types extras htarget he (hlowerLabel _)
  | numberedBase k f tau base target types extras hstep =>
    exact hlowerBaseNum target (argumentStepDescent hbaseGood hstep) htarget
      (argumentStepComputable hc hclosed hcal hbaseGood hstep hb)
  | numberedExtras k f tau base types extras target hstep =>
    exact hlowerExtra target (argumentStepDescent hextraGood hstep) htarget
      (argumentStepComputable hc hclosed hcal hextraGood hstep he)
  | bottom q hne =>
    exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Gamma context ctx scalar
      hc hclosed hcal _ hg.1.1
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySuccessorStepProof
