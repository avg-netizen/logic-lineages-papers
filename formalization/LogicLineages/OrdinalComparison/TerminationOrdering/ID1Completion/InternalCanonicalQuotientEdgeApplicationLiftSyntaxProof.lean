module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCanonicalQuotientEdgeApplicationLift
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalStepGuardSupportProof (oneRename)
open GuardedSourceSyntaxProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem typedAcceptedRename {β : Type} (data : Data)
    (x typ : OTerm α) (j : α → β) :
    (typedAccepted data x typ).relabel j =
      typedAccepted data (x.relabel j) (typ.relabel j) :=
  InternalCanonicalQuotientEdgeSelectionTypingProof.typedRename data x typ j

@[simp] theorem edgeAcceptedRename {β : Type} (data : Data)
    (x y certificate : OTerm α) (j : α → β) :
    (edgeAccepted data x y certificate).relabel j =
      edgeAccepted data (x.relabel j) (y.relabel j) (certificate.relabel j) :=
  InternalCanonicalQuotientEdgeSelectionTypingProof.edgeRename data x y certificate j

@[simp] theorem applicationGraphRename {β : Type} (data : Data)
    (out d e x a : OTerm α) (j : α → β) :
    (applicationGraph data out d e x a).relabel j =
      applicationGraph data (out.relabel j) (d.relabel j) (e.relabel j)
        (x.relabel j) (a.relabel j) := by
  exact graph4Rename (actualJ data) out d e x a j

@[simp] theorem corePremisesRename {β : Type} (data : Data) (sigma tau : Ty)
    (x y a certificate out other : OTerm α) (j : α → β) :
    (corePremises data sigma tau x y a certificate out other).relabel j =
      corePremises data sigma tau (x.relabel j) (y.relabel j) (a.relabel j)
        (certificate.relabel j) (out.relabel j) (other.relabel j) := by
  simp only [corePremises, conjunctionRename, typedAcceptedRename,
    edgeAcceptedRename, applicationGraphRename, numeralRename]

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

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
