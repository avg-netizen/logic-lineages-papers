module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedAccessibilitySupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedQuotientPaths SourceZeroNumberedComputability
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators PositiveArithmeticAccessibility PositiveArithmeticLeastSet
open SourceComputabilityFormula SourceComputabilityArrowLeastSupportProof
open SourceZeroNumberedAccessibilitySupportProof

theorem computableFromList (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2))
    (hc : Encodable.decode context = some ctx) (hclosed : SubtypeClosed (fun t => t ∈ ctx.1.2))
    (hcal : Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context))
    (values : List Nat)
    (hacc : Acc (DirectMultisetAccessibility.ReverseDirect
      (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)) values) :
    ∀ (f : Head (Fin n)) (tau : Ty)
      (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types),
      values = (argumentCodes ctx.1.1 ctx.1.2 base ++ argumentCodes ctx.1.1 ctx.1.2 extras).map Prod.snd →
      InUniverse ctx.1.1 ctx.1.2 (.numbered 0 f tau base types extras) →
      (∀ p ∈ argumentCodes ctx.1.1 ctx.1.2 base ++ argumentCodes ctx.1.1 ctx.1.2 extras,
        Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context p.1 p.2) →
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau
        (representativeCode ctx.1.1 ctx.1.2 ⟨tau,.numbered 0 f tau base types extras⟩) := by
  induction hacc with
  | intro values h ih =>
    intro f tau base types extras hvalues hgood hmembers
    apply SourceNeutralExpansionProof.actualNeutralComputabilityExpansion n arity Gamma context ctx scalar
      hc hclosed hcal tau (.numbered 0 f tau base types extras) hgood rfl
    intro y hy
    have hp := (relationCalibration n arity Gamma context ctx hc _ y).mp hy
    obtain ⟨z,hz,hsuffix⟩ := (NumberedNonLambdaPathsProof.actualPositiveFirstEdge _ _ _).mp hp
    have hcz : Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context tau z := by
      rcases SourceZeroNumberedEdgeProof.actualZeroNumberedEdge n arity ctx.1.1 ctx.1.2 hclosed
        (NumberedCopyCertificate.tableAbove ctx.2) Gamma f tau base types extras z hgood hz with
          hb | ⟨g,base',types',extras',hgood',hzcode,hreplace⟩
      · rw [hb]
        exact SourceBottomSpineComputabilityProof.actualBottomComputable n arity Gamma context ctx scalar
          hc hclosed hcal tau hgood.1.1
      · rw [hzcode]
        have hd : DirectMultisetAccessibility.ReverseDirect
            (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)
            ((argumentCodes ctx.1.1 ctx.1.2 base' ++ argumentCodes ctx.1.1 ctx.1.2 extras').map Prod.snd) values := by
          rw [hvalues]
          exact replacementDirect hreplace
        apply ih _ hd g tau base' types' extras' rfl hgood'
        exact replacementPreservesMembers
          (Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context)
          (fun sigma x y hcx hxy => SourceComputabilityDownwardProof.actualComputabilityDownward
            n arity Gamma context ctx scalar hc hclosed hcal sigma x y hcx
            ((relationCalibration n arity Gamma context ctx hc x y).mpr (.step hxy)))
          hreplace hmembers
    rcases hsuffix with he | hr
    · exact he ▸ hcz
    · exact SourceComputabilityDownwardProof.actualComputabilityDownward n arity Gamma context ctx scalar
        hc hclosed hcal tau z y hcz ((relationCalibration n arity Gamma context ctx hc z y).mpr hr)

theorem actualZeroNumberedComputable : SourceZeroNumberedComputabilityTargets.ActualZeroNumberedComputable := by
  intro n arity Gamma context ctx scalar hc hclosed hcal f tau base types extras hgood hcomp
  have hm : ∀ p ∈ argumentCodes ctx.1.1 ctx.1.2 base ++ argumentCodes ctx.1.1 ctx.1.2 extras,
      Computable n arity Gamma (fun x => x ∈ leastSet scalar context) context p.1 p.2 := by
    intro p hp
    have hp' : p ∈ (argumentList base ++ argumentList extras).map
        (fun q => (q.1,representativeCode ctx.1.1 ctx.1.2 q)) := by
      simpa only [List.map_append,argumentCodes] using hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
    exact hcomp q hq
  have hmembers : DirectMultisetAccessibleSubtype.MembersAccessible
      (QuotientDominationCertificates.relation n arity ctx.1.1 ctx.1.2 Gamma ctx.2)
      ((argumentCodes ctx.1.1 ctx.1.2 base ++ argumentCodes ctx.1.1 ctx.1.2 extras).map Prod.snd) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    exact quotientAccessible n arity Gamma context ctx hc p.2
      (SourceComputabilityLeastProof.actualComputabilityAccessible n arity Gamma context ctx scalar
        hc hclosed hcal p.1 p.2 (hm p hp))
  exact computableFromList n arity Gamma context ctx scalar hc hclosed hcal _
    (SourceDirectAccessibilityProof.actualListAccessibility n arity Gamma ctx _ hmembers)
    f tau base types extras rfl hgood hm
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceZeroNumberedComputabilityProof
