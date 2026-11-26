module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilitySupportStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityStatementChecks
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication
open NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedWindowEquivalence NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceZeroNumberedComputability SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceConstructorComputabilityExpansionProof SourceConstructorComputabilityOrdinaryStepProof
open SourceConstructorComputabilityInduction RankedPrecedenceCertificate
variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

theorem fixedNumbered : SourceRankedConstructorComputabilityTargets.ActualNumberedConstructorComputable :=
  SourceRankedConstructorComputabilityProof.actualNumberedConstructorComputable

theorem fixedOrdinary : SourceRankedConstructorComputabilityTargets.ActualOrdinaryConstructorComputable :=
  SourceRankedConstructorComputabilityProof.actualOrdinaryConstructorComputable

#print axioms fixedNumbered
#print axioms fixedOrdinary

theorem fixed_selfArgumentsComputable (k : Nat) (f : Head (Fin n))
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments (Fin n) arity Gamma extraTypes)
    (types : List Ty)
    (h : ∀ tau ∈ types, TermC context ctx scalar (.numbered k f tau base extraTypes extras)) :
    ArgumentsC context ctx scalar (selfArguments k f base extraTypes extras types) := by
  exact SourceConstructorComputabilityApplicationProof.selfArgumentsComputable (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (k := k) (f := f) (base := base) (extraTypes := extraTypes) (extras := extras) (types := types) (h := h)

theorem fixed_completeApplicationComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (types : List Ty) (tau : Ty) (q : AuxTerm (Fin n) arity Gamma (arrows types tau))
    (args : AuxArguments (Fin n) arity Gamma types)
    (hgq : InUniverse ctx.1.1 ctx.1.2 q)
    (hga : NumberedUniverseBindingTargets.GoodArguments (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) args)
    (hcq : TermC context ctx scalar q) (hca : ArgumentsC context ctx scalar args) :
    TermC context ctx scalar (applyArguments q args) := by
  exact SourceConstructorComputabilityApplicationProof.completeApplicationComputable (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (types := types) (tau := tau) (q := q) (args := args) (hgq := hgq) (hga := hga) (hcq := hcq) (hca := hca)

theorem fixed_openedComputable
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (k : Nat) (f : Head (Fin n)) (sigma tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
    (hg : InUniverse ctx.1.1 ctx.1.2 (.lam (openNumbered k f sigma tau base types extras)))
    (he : ArgumentsC context ctx scalar extras)
    (hlower : ∀ (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types' extras') →
      ArgumentsC context ctx scalar extras' → TermC context ctx scalar (.numbered k f tau base types' extras')) :
    TermC context ctx scalar (.lam (openNumbered k f sigma tau base types extras)) := by
  exact SourceConstructorComputabilityApplicationProof.openedComputable (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (k := k) (f := f) (sigma := sigma) (tau := tau) (base := base) (types := types) (extras := extras) (hg := hg) (he := he) (hlower := hlower)

theorem fixed_numberedSuccessorStep
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
  exact SourceConstructorComputabilitySuccessorStepProof.numberedSuccessorStep (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (rank := rank) (hrank := hrank) (k := k) (f := f) (tau := tau) (base := base) (types := types) (extras := extras) (hg := hg) (hb := hb) (he := he) (hlowerHead := hlowerHead) (hlowerBaseOrd := hlowerBaseOrd) (hlowerBaseNum := hlowerBaseNum) (hlowerLabel := hlowerLabel) (hlowerExtra := hlowerExtra)

theorem fixed_ordinaryStepGeneral
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {tau : Ty} {q r : AuxTerm (Fin n) arity Gamma tau}
    (hs : WindowStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma tau q r) :
    OrdinaryPremises context ctx scalar ⟨tau,q⟩ → TermC context ctx scalar r := by
  exact SourceConstructorComputabilityOrdinaryStepProof.ordinaryStepGeneral (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (tau := tau) (q := q) (r := r) (hs := hs)

theorem fixed_ordinaryStep
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
  exact SourceConstructorComputabilityOrdinaryStepProof.ordinaryStep (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (f := f) (base := base) (hg := hg) (hb := hb) (hfinite := hfinite) (hlowerBase := hlowerBase)

theorem fixed_numberedAtSuccessor
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (head : Nat) (values : List Nat) (k : Nat)
    (hlowerHead : ∀ head' : Nat, head' < head → ∀ values' : List Nat,
      Acc (Descent arity Gamma ctx) values' → AtBase arity Gamma context ctx scalar rank head' values')
    (hlowerBase : ∀ values' : List Nat, Descent arity Gamma ctx values' values →
      AtBase arity Gamma context ctx scalar rank head values')
    (hlowerLabel : NumberedAt arity Gamma context ctx scalar rank head values k) :
    NumberedAt arity Gamma context ctx scalar rank head values (k+1) := by
  exact SourceConstructorComputabilityExtraInductionProof.numberedAtSuccessor (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (rank := rank) (hrank := hrank) (head := head) (values := values) (k := k) (hlowerHead := hlowerHead) (hlowerBase := hlowerBase) (hlowerLabel := hlowerLabel)

theorem fixed_jointByRank
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true) :
    ∀ head : Nat, ∀ values : List Nat, Acc (Descent arity Gamma ctx) values →
      AtBase arity Gamma context ctx scalar rank head values := by
  exact SourceConstructorComputabilityJointInductionProof.jointByRank (n := n) (arity := arity) (Gamma := Gamma) (context := context) (ctx := ctx) (scalar := scalar) (hc := hc) (hclosed := hclosed) (hcal := hcal) (rank := rank) (hrank := hrank)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityStatementChecks
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceRankedConstructorComputabilityStatementChecks
