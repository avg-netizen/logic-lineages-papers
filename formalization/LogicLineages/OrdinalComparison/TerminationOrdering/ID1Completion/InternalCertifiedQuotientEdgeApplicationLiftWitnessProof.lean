module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftWitnessProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalRepresentativeApplicationCongruenceSupportProof GuardedSourceSyntaxProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem coreAcceptedRename {β : Type} (data : Data)
    (x y certificate : OTerm α) (j : α → β) :
    (coreAccepted data x y certificate).relabel j =
      coreAccepted data (x.relabel j) (y.relabel j) (certificate.relabel j) := by
  change (graph3 (InternalQuotientEdgeChecker.checker
    (InternalCertifiedSourceGuardSelection.edgeData data)) InternalOriginalStepGuard.one
    x y certificate).relabel j = _
  rw [graph3Rename,oneRename]
  rfl

@[simp] theorem corePremisesRename {β : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other : OTerm α) (j : α → β) :
    (corePremises data sigma tau x y a certificate out other).relabel j =
      corePremises data sigma tau (x.relabel j) (y.relabel j) (a.relabel j)
        (certificate.relabel j) (out.relabel j) (other.relabel j) := by
  simp only [corePremises,InternalCertifiedSourceGuardSelection.typedAccepted,
    conjunctionRename,graph2Rename,coreAcceptedRename,graph4Rename,oneRename,numeralRename]

/-- Six actual queries simultaneously bind the original raw fields and their
original lifted values. None is a semantic evaluation witness. -/
def queries : Fin 6 → Program 4 :=
  ![certificateField source,certificateField target,certificateField step,
    sourceApplication,targetApplication,InternalApplicationCertificateConstructors.liftedStep]

theorem applicationFieldRecover (p : Program 1) (field out d e a certificate : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph4 (certificateField p) field d e a certificate)))
    (hp : Nonempty (Derivation body Gamma (graph4
      (.composition application ![.projection 0,.projection 1,certificateField p,.projection 2])
      out d e a certificate))) :
    Nonempty (Derivation body Gamma (graph4 application out d e field a)) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))
  apply compositionRecover application ![.projection 0,.projection 1,certificateField p,.projection 2]
    out xs (Fin.cons d (Fin.cons e (Fin.cons field (Fin.cons a Fin.elim0)))) hp
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases hf (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q)))) i

theorem constructorsAtQueries (d e a certificate : OTerm α) (ys : Fin 6 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation body Gamma
      (programGraph (queries i) (ys i)
        (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0))))))) :
    Nonempty (Derivation body Gamma
      (InternalApplicationCertificateConstructors.liftPremises d e a certificate
        (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5))) := by
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))
  have hsource := InternalOriginalTypedCarrierSupportProof.atRecover source 3 (ys 0) xs (hq 0)
  have htarget := InternalOriginalTypedCarrierSupportProof.atRecover target 3 (ys 1) xs (hq 1)
  have hstep := InternalOriginalTypedCarrierSupportProof.atRecover step 3 (ys 2) xs (hq 2)
  have hselectors := andIntro hsource (andIntro htarget hstep)
  have hsapp := applicationFieldRecover source (ys 0) (ys 3) d e a certificate (hq 0) (hq 3)
  have htapp := applicationFieldRecover target (ys 1) (ys 4) d e a certificate (hq 1) (hq 4)
  have hk := unaryRecover stepLift (certificateField step) (ys 5) (ys 2) xs (hq 5) (hq 2)
  exact andIntro (edgeReconstruction certificate (ys 0) (ys 1) (ys 2) hselectors)
    (andIntro hsapp (andIntro htapp hk))

/-- Internal totality and exact edgeLift commutation eliminate every raw
witness while preserving the supplied certificate and the two C outputs. -/
theorem coreLift (S : List Ty) (data : Data)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S data.member)
    (hc : SubtypeClosed (fun typ => typ ∈ S)) (sigma tau : Ty)
    (x y a certificate out other lifted : OTerm α)
    (hp : Nonempty (Derivation body Gamma
      (InternalCertifiedQuotientEdgeApplicationLift.liftPremises
        data sigma tau x y a certificate out other lifted))) :
    Nonempty (Derivation body Gamma (coreAccepted data out other lifted)) := by
  apply queryCases queries
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons a (Fin.cons certificate Fin.elim0)))) _
  intro β j ys Delta hj hq
  rw [coreAcceptedRename]
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
  exact InternalCertifiedQuotientEdgeApplicationLiftEncodedProof.encodedLift S data hm hc sigma tau
    (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
    (out.relabel j) (other.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) hcore (andIntro hw he)

theorem actualOriginalCertifiedQuotientEdgeApplicationLift :
    InternalCertifiedQuotientEdgeApplicationLiftTargets.ActualOriginalCertifiedQuotientEdgeApplicationLift := by
  intro S data hm hc body sigma tau α x y a certificate out other lifted
  let premise := InternalCertifiedQuotientEdgeApplicationLift.liftPremises
    data sigma tau x y a certificate out other lifted
  obtain ⟨result⟩ := coreLift S data hm hc sigma tau x y a certificate out other lifted
    (body := body) (Gamma := [premise]) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction result⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftWitnessProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedQuotientEdgeApplicationLiftWitnessProof
