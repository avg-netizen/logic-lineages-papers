module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowVertexDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftCompatibilityProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCanonicalFixedWindowVertexDispatch
open InternalCanonicalFixedWindowVertexDispatchSupportProof
open InternalCanonicalFixedWindowVertexDispatchInvariantProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionEqualityProof SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Original arithmetic equality substitution at four input coordinates.
The Program and its supplied output are unchanged. -/
theorem fourInputsTransport (p : Program 4)
    (out a b c d a' b' c' d' : OTerm α)
    (ha : Nonempty (Derivation body Delta (equal a a')))
    (hb : Nonempty (Derivation body Delta (equal b b')))
    (hc : Nonempty (Derivation body Delta (equal c c')))
    (hd : Nonempty (Derivation body Delta (equal d d')))
    (h : Nonempty (Derivation body Delta (graph4 p out a b c d))) :
    Nonempty (Derivation body Delta (graph4 p out a' b' c' d')) := by
  apply graphInputTransport body α 4 Delta (OrdinaryArithmetic.graphFormula p) out
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Fin.elim0))))
    (Fin.cons a' (Fin.cons b' (Fin.cons c' (Fin.cons d' Fin.elim0)))) _ h
  intro i
  exact Fin.cases ha (Fin.cases hb (Fin.cases hc (Fin.cases hd (fun j => Fin.elim0 j)))) i

/-- Both endpoint activations and exact closed coordinates are derived from
the source invariant and SAME Edge. Only then is the checked original actualJ
rule used, with the supplied original edgeLift output and RAW argument. -/
theorem actualInternalCanonicalFixedWindowEdgeCompatibility :
    InternalCanonicalFixedWindowPathLiftTargets.ActualInternalCanonicalFixedWindowEdgeCompatibility := by
  intro S data hm hclosed window oldVertex body sigma tau α ps x y certificate out other lifted
  let premise :=
    InternalApplicationPathLift.invariantAt (invariant window data sigma tau) ps x ⊓
      (InternalPathChecker.edgeGraph (InternalCanonicalQuotientEdgeSelection.edgeChecker data) x y certificate ⊓
        (InternalApplicationPathLift.vertexAt (vertex window data oldVertex) ps out x ⊓
          (InternalApplicationPathLift.vertexAt (vertex window data oldVertex) ps other y ⊓
            InternalApplicationPathLift.liftedEdgeAt ps lifted certificate)))
  have hp : Nonempty (Derivation body [premise] premise) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hix := andLeft hp
  have hedge := andLeft (andRight hp)
  have hvertices := andRight (andRight hp)
  have hiy := invariantPreserve window data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) x y certificate hix hedge
  have hax := invariantActivation window data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) x hix
  have hay := invariantActivation window data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) y hiy
  have hout := vertexRecover window data oldVertex
    (ps 0) (ps 1) (ps 2) (ps 3) x out hax (andLeft hvertices)
  have hother := vertexRecover window data oldVertex
    (ps 0) (ps 1) (ps 2) (ps 3) y other hay (andLeft (andRight hvertices))
  have hf := invariantRecover window data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) x hix
  have hd := andLeft (andRight hf)
  have he := andLeft (andRight (andRight hf))
  have hx := andLeft (andRight (andRight (andRight hf)))
  have ha := andRight (andRight (andRight (andRight hf)))
  have houtClosed := fourInputsTransport (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
    out (ps 1) (ps 2) x (ps 3)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x (ps 3)
    hd he (equalReflexive x) (equalReflexive (ps 3)) hout
  have hotherClosed := fourInputsTransport (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
    other (ps 1) (ps 2) y (ps 3)
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y (ps 3)
    hd he (equalReflexive y) (equalReflexive (ps 3)) hother
  have hliftClosed := fourInputsTransport InternalApplicationCertificateConstructors.edgeLift
    lifted (ps 1) (ps 2) (ps 3) certificate
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) (ps 3) certificate
    hd he (equalReflexive (ps 3)) (equalReflexive certificate)
    (andRight (andRight hvertices))
  have hlocal : Nonempty (Derivation body [premise]
      (InternalCanonicalQuotientEdgeApplicationLift.liftPremises data sigma tau
        x y (ps 3) certificate out other lifted)) :=
    andIntro (andIntro hx (andIntro ha (andIntro hedge (andIntro houtClosed hotherClosed)))) hliftClosed
  obtain ⟨hlocal⟩ := hlocal
  obtain ⟨hrule⟩ :=
    InternalCanonicalQuotientEdgeApplicationLiftProof.actualOriginalCanonicalQuotientEdgeApplicationLift
      S data hm hclosed body sigma tau α [premise] x y (ps 3) certificate out other lifted
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hrule hlocal)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftCompatibilityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalFixedWindowPathLiftCompatibilityProof
