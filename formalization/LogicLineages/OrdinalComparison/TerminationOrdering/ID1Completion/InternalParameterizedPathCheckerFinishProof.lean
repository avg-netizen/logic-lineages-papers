module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerFinishProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalPathCheckerBranchProof
open InternalPathCheckerFinishProof (pairLeft pairRight)
open InternalListCodec InternalListCodecSupportProof InternalRawListRecursionSupportProof
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem summaryHeadValue (x y state raw result parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryHead raw (quadruple x y state parameter))) := by
  apply compositionValue headCode (fun _ : Fin 1 => .projection 2)
    raw (quadruple x y state parameter) (Fin.cons state Fin.elim0) (consHead state raw result hc)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 (quadruple x y state parameter)

theorem summaryVertexValue (x y state raw result vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryVertex vertex (quadruple x y state parameter))) := by
  apply compositionValue InternalUnpair.left (fun _ : Fin 1 => summaryHead)
    vertex (quadruple x y state parameter) (Fin.cons raw Fin.elim0) (pairLeft raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact summaryHeadValue x y state raw result parameter hc

theorem summaryCertificateValue (x y state raw result vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryCertificate certificate (quadruple x y state parameter))) := by
  apply compositionValue InternalUnpair.right (fun _ : Fin 1 => summaryHead)
    certificate (quadruple x y state parameter) (Fin.cons raw Fin.elim0) (pairRight raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact summaryHeadValue x y state raw result parameter hc

theorem summaryTailValue (x y state raw result parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryTail result (quadruple x y state parameter))) := by
  apply compositionValue tailCode (fun _ : Fin 1 => .projection 2)
    result (quadruple x y state parameter) (Fin.cons state Fin.elim0) (consTail state raw result hc)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 (quadruple x y state parameter)

theorem edgeAtSummaryValue (edge : Program 4) (x y state raw result vertex certificate out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (programGraph edge out (quadruple x vertex certificate parameter)))) :
    Nonempty (Derivation body Gamma (programGraph (edgeAtSummary edge) out (quadruple x y state parameter))) := by
  apply compositionValue edge (quadruple (.projection 0) summaryVertex summaryCertificate (.projection 3))
    out (quadruple x y state parameter) (quadruple x vertex certificate parameter) he
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y state parameter))
    (Fin.cases (summaryVertexValue x y state raw result vertex certificate parameter hp hc)
      (Fin.cases (summaryCertificateValue x y state raw result vertex certificate parameter hp hc)
        (Fin.cases (projectionValue 3 (quadruple x y state parameter)) (fun q => Fin.elim0 q)))) i

theorem edgeAtSummaryRecover (edge : Program 4) (x y state raw result vertex certificate out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (programGraph (edgeAtSummary edge) out (quadruple x y state parameter)))) :
    Nonempty (Derivation body Gamma (programGraph edge out (quadruple x vertex certificate parameter))) := by
  apply compositionRecover edge (quadruple (.projection 0) summaryVertex summaryCertificate (.projection 3))
    out (quadruple x y state parameter) (quadruple x vertex certificate parameter) he
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y state parameter))
    (Fin.cases (summaryVertexValue x y state raw result vertex certificate parameter hp hc)
      (Fin.cases (summaryCertificateValue x y state raw result vertex certificate parameter hp hc)
        (Fin.cases (projectionValue 3 (quadruple x y state parameter)) (fun q => Fin.elim0 q)))) i

theorem endpointsValue (out x y state parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.equalityTest out
      (Fin.cons x (Fin.cons y Fin.elim0))))) :
    Nonempty (Derivation body Gamma (programGraph endpointsEqual out (quadruple x y state parameter))) := by
  apply compositionValue InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)) out
    (quadruple x y state parameter) (Fin.cons x (Fin.cons y Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y state parameter))
    (Fin.cases (projectionValue 1 (quadruple x y state parameter)) (fun q => Fin.elim0 q)) i

theorem endpointsRecover (out x y state parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph endpointsEqual out (quadruple x y state parameter)))) :
    Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.equalityTest out
      (Fin.cons x (Fin.cons y Fin.elim0)))) := by
  apply compositionRecover InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)) out
    (quadruple x y state parameter) (Fin.cons x (Fin.cons y Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 0 (quadruple x y state parameter))
    (Fin.cases (projectionValue 1 (quadruple x y state parameter)) (fun q => Fin.elim0 q)) i

theorem finishZeroValue (edge : Program 4) (positive : Bool) (out x y parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (emptyFinish positive) out (quadruple x y z parameter)))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive out x y z parameter)) :=
  zeroBranchIntro (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    out (quadruple x y z parameter) (projectionValue 2 (quadruple x y z parameter)) h

theorem finishZeroRecover (edge : Program 4) (positive : Bool) (out x y parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (finishGraph edge positive out x y z parameter))) :
    Nonempty (Derivation body Gamma (programGraph (emptyFinish positive) out (quadruple x y z parameter))) :=
  zeroBranchElim (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    out (quadruple x y z parameter) (projectionValue 2 (quadruple x y z parameter)) h

/-- A nonempty summary accepts precisely its actual edge and its stored
suffix value equal to one. No Boolean range assumption is needed. -/
theorem finishConsAccept (edge : Program 4) (positive : Bool)
    (x y state raw result vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (edgeGraph edge x vertex certificate parameter)))
    (hr : Nonempty (Derivation body Gamma (eqn result (suc z)))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive (suc z) x y state parameter)) := by
  have ha := edgeAtSummaryValue edge x y state raw result vertex certificate (suc z) parameter hp hc he
  have hb := outputTransport summaryTail result (suc z) (quadruple x y state parameter) hr
    (summaryTailValue x y state raw result parameter hc)
  have hw := conjunctionAccept (edgeAtSummary edge) summaryTail (quadruple x y state parameter) ha hb
  obtain ⟨hv⟩ := consDestruction state raw result hc
  exact nonzeroBranchIntro (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    (suc z) state (quadruple x y state parameter) (projectionValue 2 (quadruple x y state parameter))
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hv)⟩ hw

theorem finishConsRecover (edge : Program 4) (positive : Bool)
    (x y state raw result vertex certificate parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (h : Nonempty (Derivation body Gamma (finishGraph edge positive (suc z) x y state parameter))) :
    Nonempty (Derivation body Gamma (edgeGraph edge x vertex certificate parameter ⊓ eqn result (suc z))) := by
  obtain ⟨hv⟩ := consDestruction state raw result hc
  have hw := nonzeroBranchElim (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    (suc z) state (quadruple x y state parameter) (projectionValue 2 (quadruple x y state parameter))
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hv)⟩ h
  obtain ⟨hab⟩ := conjunctionRecover (edgeAtSummary edge) summaryTail (quadruple x y state parameter) hw
  obtain ⟨ha⟩ := edgeAtSummaryRecover edge x y state raw result vertex certificate (suc z) parameter
    hp hc ⟨Derivation.conjunctionLeft hab⟩
  obtain ⟨hb⟩ := valueUnique summaryTail result (suc z) (quadruple x y state parameter)
    (summaryTailValue x y state raw result parameter hc) ⟨Derivation.conjunctionRight hab⟩
  exact ⟨Derivation.conjunctionIntroduction ha hb⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerFinishProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerFinishProof
