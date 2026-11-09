module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalQuotientEdgeApplicationLift
open InternalParameterizedCanonicalQuotientEdgeApplicationLiftSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof (queries constructorsAtQueries)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Six original total programs bind every raw witness. Elimination retains
the supplied actualJ outputs, the identical raw argument and symbolic p. -/
theorem applicationLift (data : Data) (oldStep : Program 4)
    (arrow d e x y a certificate out other lifted parameter : OTerm α)
    (hcore : Nonempty (Derivation body Gamma
      (corePremises data oldStep arrow d e x y a certificate out other parameter)))
    (hlift : Nonempty (Derivation body Gamma
      (InternalApplicationCertificateConstructors.graph4
        InternalApplicationCertificateConstructors.edgeLift lifted d e a certificate))) :
    Nonempty (Derivation body Gamma (edgeAccepted data oldStep out other lifted parameter)) := by
  apply queryCases queries (Fin.cons d (Fin.cons e (Fin.cons a (Fin.cons certificate Fin.elim0)))) _
  intro β j ys Delta hj hq
  rw [edgeAcceptedRename]
  have hcore' := renameInto hcore j Delta hj
  have hlift' := renameInto hlift j Delta hj
  rw [corePremisesRename] at hcore'
  rw [graph4Rename] at hlift'
  simp only [consTermRename,emptyRename] at hq
  have hw := constructorsAtQueries (d.relabel j) (e.relabel j)
    (a.relabel j) (certificate.relabel j) ys hq
  have he := edgeLiftForward (d.relabel j) (e.relabel j)
    (a.relabel j) (certificate.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) hw hlift'
  exact InternalParameterizedCanonicalQuotientEdgeApplicationLiftEncodedProof.encodedLift
    data oldStep (arrow.relabel j) (d.relabel j) (e.relabel j)
    (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
    (out.relabel j) (other.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) (parameter.relabel j) hcore' (andIntro hw he)

theorem actualParameterizedCanonicalQuotientEdgeApplicationLift :
    InternalParameterizedCanonicalQuotientEdgeApplicationLiftTargets.ActualParameterizedCanonicalQuotientEdgeApplicationLift := by
  intro body data oldStep α Delta arrow d e x y a certificate out other lifted parameter
  let P := liftPremises data oldStep arrow d e x y a certificate out other lifted parameter
  have h : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hresult⟩ := applicationLift data oldStep arrow d e x y a certificate out other lifted parameter
    (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftWitnessProof
