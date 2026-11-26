module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityMembersProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExpansionProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedWindowReduction NumberedWindowEquivalence NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility
open SourceZeroNumberedComputability SourceConstructorComputability SourceConstructorComputabilityMembersProof
open SourceComputabilityArrowLeastSupportProof RankedPrecedenceCertificate

variable {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {context : Nat}
  {ctx : Context n} {scalar : Positive (Fin 2)}

/-- An internal induction conclusion for the actual one-step reducts of one
packed term. It is never an endpoint hypothesis. -/
def StepC (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (q : Packed (Fin n) arity Gamma) : Prop :=
  ∀ r : AuxTerm (Fin n) arity Gamma q.1,
    WindowStep (Fin n) arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma q.1 q.2 r →
    TermC context ctx scalar r

theorem neutralFromPrimarySteps
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    {tau : Ty} (q : AuxTerm (Fin n) arity Gamma tau)
    (hg : InUniverse ctx.1.1 ctx.1.2 q) (hn : NumberedPrimaryShapes.isLambda q = false)
    (hstep : ∀ p : Packed (Fin n) arity Gamma, InUniverse ctx.1.1 ctx.1.2 p.2 →
      WindowPrimary (Fin n) arity ctx.1.1 ctx.1.2 Gamma ⟨tau,q⟩ p → StepC context ctx scalar p) :
    TermC context ctx scalar q := by
  apply SourceNeutralExpansionProof.actualNeutralComputabilityExpansion n arity Gamma context ctx scalar
    hc hclosed hcal tau q hg hn
  intro y hy
  have hp := (relationCalibration n arity Gamma context ctx hc _ y).mp hy
  obtain ⟨z,hz,hsuffix⟩ := (NumberedNonLambdaPathsProof.actualPositiveFirstEdge _ _ _).mp hp
  have hcz : CodeC n arity Gamma context scalar tau z := by
    obtain ⟨rho,a,b,ha,hs,hcode,hb⟩ := hz
    have hprimary := (NumberedLeastCodeRepresentativeProof.representativeEquality
      n arity ctx.1.1 ctx.1.2 hclosed Gamma ⟨tau,q⟩ ⟨rho,a⟩ hg ha).mp hcode.symm
    have ht : tau = rho := NumberedPrimaryEquivalenceProof.primaryTypePreservation (Fin n) arity Gamma _ _
      (NumberedWindowEquivalenceProof.actualPrimaryErasure (Fin n) arity ctx.1.1 ctx.1.2 Gamma _ _ hprimary)
    cases ht
    rw [←hb]
    exact hstep ⟨tau,a⟩ ha hprimary b hs
  rcases hsuffix with he | hr
  · exact he ▸ hcz
  · exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar
      hc hclosed hcal tau z y hcz ((relationCalibration n arity Gamma context ctx hc z y).mpr hr)

theorem ordinaryExpansion
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (hg : InUniverse ctx.1.1 ctx.1.2 (.ordinary f base)) (hb : ArgumentsC context ctx scalar base)
    (hstep : ∀ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g)),
      headRank rank g = headRank rank f → (ArgumentValues ctx base').Perm (ArgumentValues ctx base) →
      InUniverse ctx.1.1 ctx.1.2 (.ordinary g base') → ArgumentsC context ctx scalar base' →
      StepC context ctx scalar ⟨headResult g,.ordinary g base'⟩) :
    TermC context ctx scalar (.ordinary f base) := by
  apply neutralFromPrimarySteps hc hclosed hcal (.ordinary f base) hg rfl
  intro p hp hprimary
  obtain ⟨g,base',he,hr,hbase⟩ :=
    SourceConstructorPrimaryMeasuresProof.actualPrimaryOrdinaryMeasures
      n arity ctx.1.1 ctx.1.2 hclosed ctx.2 rank hrank Gamma f base p hg hprimary
  have hgood : InUniverse ctx.1.1 ctx.1.2 (.ordinary g base') := by
    rw [he] at hp
    exact hp
  rw [he]
  exact hstep g base' hr.symm (hbase.map Prod.snd).symm hgood (argumentsCPerm hbase hb)

theorem numberedExpansion
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (rank : Fin n → Fin n) (hrank : rankCertificateTest ctx.2 rank = true)
    (k : Nat) (f : Head (Fin n)) (tau : Ty)
    (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types)
    (hg : InUniverse ctx.1.1 ctx.1.2 (.numbered k f tau base types extras))
    (hb : ArgumentsC context ctx scalar base) (he : ArgumentsC context ctx scalar extras)
    (hstep : ∀ (g : Head (Fin n)) (base' : AuxArguments (Fin n) arity Gamma (headArguments arity g))
      (types' : List Ty) (extras' : AuxArguments (Fin n) arity Gamma types'),
      headRank rank g = headRank rank f → (ArgumentValues ctx base').Perm (ArgumentValues ctx base) →
      ArgumentValues ctx extras' = ArgumentValues ctx extras →
      InUniverse ctx.1.1 ctx.1.2 (.numbered k g tau base' types' extras') →
      ArgumentsC context ctx scalar base' → ArgumentsC context ctx scalar extras' →
      StepC context ctx scalar ⟨tau,.numbered k g tau base' types' extras'⟩) :
    TermC context ctx scalar (.numbered k f tau base types extras) := by
  apply neutralFromPrimarySteps hc hclosed hcal (.numbered k f tau base types extras) hg rfl
  intro p hp hprimary
  obtain ⟨g,base',types',extras',hpcode,hr,hbase,hextra⟩ :=
    SourceConstructorPrimaryMeasuresProof.actualPrimaryNumberedMeasures
      n arity ctx.1.1 ctx.1.2 hclosed ctx.2 rank hrank Gamma k f tau base types extras p hg hprimary
  have hgood : InUniverse ctx.1.1 ctx.1.2 (.numbered k g tau base' types' extras') := by
    rw [hpcode] at hp
    exact hp
  rw [hpcode]
  exact hstep g base' types' extras' hr.symm (hbase.map Prod.snd).symm
    (congrArg (List.map Prod.snd) hextra).symm hgood (argumentsCPerm hbase hb)
    (argumentsCPerm (List.Perm.of_eq hextra) he)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorComputabilityExpansionProof
