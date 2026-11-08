module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftWitnessProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCanonicalQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof GuardedSourceSyntaxProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Internal totality and exact edgeLift commutation eliminate every raw
witness while preserving the supplied certificate and the two C outputs. -/
theorem coreLift (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other lifted : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalCanonicalQuotientEdgeApplicationLift.liftPremises
        data sigma tau x y a certificate out other lifted))) :
    Nonempty (Derivation body Gamma (edgeAccepted data out other lifted)) := by
  apply queryCases queries
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons a (Fin.cons certificate Fin.elim0)))) _
  intro β j ys Delta hj hq
  rw [edgeAcceptedRename]
  have hcore := renameInto (andLeft hp) j Delta hj
  have hlift := renameInto (andRight hp) j Delta hj
  rw [corePremisesRename] at hcore
  simp only [graph4Rename,numeralRename] at hlift
  simp only [consTermRename,emptyRename,numeralRename] at hq
  have hw := constructorsAtQueries (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (a.relabel j) (certificate.relabel j) ys hq
  have he := edgeLiftForward (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (a.relabel j) (certificate.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) hw hlift
  exact InternalCanonicalQuotientEdgeApplicationLiftEncodedProof.encodedLift S data hm hc sigma tau
    (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
    (out.relabel j) (other.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) hcore (andIntro hw he)

theorem actualOriginalCanonicalQuotientEdgeApplicationLift :
    InternalCanonicalQuotientEdgeApplicationLiftTargets.ActualOriginalCanonicalQuotientEdgeApplicationLift := by
  intro S data hm hc body sigma tau α Delta x y a certificate out other lifted
  let premise := InternalCanonicalQuotientEdgeApplicationLift.liftPremises
    data sigma tau x y a certificate out other lifted
  obtain ⟨result⟩ := coreLift S data hm hc sigma tau x y a certificate out other lifted
    (body := body) (Gamma := premise :: Delta) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftWitnessProof
