module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication
open SourceComputabilityFormula SourceBottomSpineComputabilitySupportProof SourceConditionalLambdaSupportProof

theorem lambdaInduction (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (sigma tau : Ty) (value : Nat)
    (hacc : Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma :: Gamma)) source successor) value) :
    ∀ (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau),
    representativeCode ctx.1.1 ctx.1.2 ⟨tau,body⟩ = value → InUniverse ctx.1.1 ctx.1.2 (.lam body) →
    (∀ a : AuxTerm (Fin n) arity Gamma sigma, InUniverse ctx.1.1 ctx.1.2 a →
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context sigma (representativeCode ctx.1.1 ctx.1.2 ⟨sigma,a⟩) →
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body (singleSubstitution a)⟩)) →
    Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context (.arrow sigma tau)
      (representativeCode ctx.1.1 ctx.1.2 ⟨.arrow sigma tau,.lam body⟩) := by
  induction hacc with
  | intro value hacc ih =>
    intro body he hl hinst
    have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hl.1.2.2,hl.2⟩
    refine ⟨encodedTypedOfTerm n arity Gamma context ctx hc hclosed (.arrow sigma tau) (.lam body) hl, ?_⟩
    intro u hu
    have htyped := SourceComputabilityFormulaProof.actualComputabilityTypedness n arity Gamma
      (fun x => x ∈ leastSet scalar context) context sigma u hu
    obtain ⟨a,ha,hrep⟩ := encodedTypedWitness n arity Gamma context ctx hc hclosed sigma u htyped
    have hca := hrep.symm ▸ hu
    have happ := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau (.lam body) a hl ha
    refine ⟨representativeCode ctx.1.1 ctx.1.2 (applicationPacked (.lam body) a), ?_, ?_⟩
    · rw [SourceComputabilityArrowLeastSupportProof.applicationCalibration n arity Gamma context ctx hc sigma tau, ← hrep]
      exact NumberedNumericApplicationProof.canonicalApplicationCalibration n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau (.lam body) a hl ha
    · apply SourceNeutralExpansionProof.actualNeutralComputabilityExpansion n arity Gamma context ctx scalar hc hclosed hcal tau (.app (.lam body) a) happ rfl
      intro y hy
      have hp := (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc _ y).mp hy
      obtain ⟨z,hz,hrest⟩ := (NumberedNonLambdaPathsProof.actualPositiveFirstEdge _ _ _).mp hp
      have hcz : Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau z := by
        rcases NumberedBetaApplicationEdgeProof.actualBetaApplicationEdge n arity ctx.1.1 ctx.1.2 hclosed
          (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma tau body a z hl ha hz with hbot | hbeta | hbotapp | hnext
        · rw [hbot]
          have ht := NumberedUniverseOperationsProof.rootType (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) body hb
          exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Gamma context ctx scalar hc hclosed hcal tau ht
        · obtain ⟨body',a',hb',ha',hbb,haa,hout⟩ := hbeta
          have hac := (NumberedLeastCodeRepresentativeProof.representativeEquality n arity ctx.1.1 ctx.1.2 hclosed Gamma _ _ ha ha').mpr haa
          have hca' := hac ▸ hca
          have hcb := hinst a' ha' hca'
          have hbc := betaPrimaryCode n arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau body body' a' hb hb' ha' hbb
          rw [hout]
          exact hbc ▸ hcb
        · rw [hbotapp]
          have hbottom : InUniverse ctx.1.1 ctx.1.2 (AuxTerm.bottom (Symbol := Fin n) (arity := arity) (Gamma := Gamma) (.arrow sigma tau)) := ⟨hl.1.1,trivial⟩
          have hgood := NumberedQuotientApplicationProof.applicationConfinement (Fin n) arity ctx.1.1 ctx.1.2 hclosed Gamma sigma tau (.bottom (.arrow sigma tau)) a hbottom ha
          exact SourceBottomSpineComputabilityProof.actualBottomSpineComputable n arity Gamma context ctx scalar hc hclosed hcal tau
            (.app (.bottom (.arrow sigma tau)) a) hgood trivial
        · obtain ⟨next,hn,hbn,hout⟩ := hnext
          have hpath : PositivePath (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) (sigma :: Gamma))
              (representativeCode ctx.1.1 ctx.1.2 ⟨tau,body⟩) (representativeCode ctx.1.1 ctx.1.2 ⟨tau,next⟩) := .step hbn
          have hln : InUniverse ctx.1.1 ctx.1.2 (.lam next) := ⟨⟨hl.1.1,hl.1.2.1,hn.1⟩,hn.2⟩
          have hcn := ih _ (he ▸ hpath) next rfl hln (by
            intro b hbarg hcbarg
            exact SourceBetaInstanceDownwardProof.actualBetaInstanceDownward n arity Gamma context ctx scalar hc hclosed hcal
              sigma tau body next b hb hn hbarg hpath (hinst b hbarg hcbarg))
          rw [hout]
          exact applicationComputable n arity Gamma context ctx scalar hc hclosed sigma tau (.lam next) a hln ha hcn hca
      rcases hrest with heq | hr
      · exact heq ▸ hcz
      · exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar hc hclosed hcal tau z y hcz
          ((SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc z y).mpr hr)

theorem actualConditionalLambdaComputability : SourceConditionalLambdaTargets.ActualConditionalLambdaComputability := by
  intro n arity Gamma context ctx scalar hc hclosed hcal sigma tau body hl hacc hinst
  exact lambdaInduction n arity Gamma context ctx scalar hc hclosed hcal sigma tau _ hacc body rfl hl hinst

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaProof
