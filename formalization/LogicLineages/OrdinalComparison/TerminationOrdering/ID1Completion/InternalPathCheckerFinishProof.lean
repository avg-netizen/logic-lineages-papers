module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalPathChecker InternalPathCheckerSyntaxProof InternalPathCheckerBranchProof
open InternalListCodec InternalListCodecSupportProof InternalRawListRecursionSupportProof
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem pairLeft (raw vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate))) :
    Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.left vertex raw)) := by
  obtain ⟨h⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse
    body α raw vertex certificate) hp
  exact ⟨Derivation.conjunctionLeft h⟩

theorem pairRight (raw vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate))) :
    Nonempty (Derivation body Gamma (unaryGraph InternalUnpair.right certificate raw)) := by
  obtain ⟨h⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse
    body α raw vertex certificate) hp
  exact ⟨Derivation.conjunctionRight h⟩

theorem summaryHeadValue (x y state raw result : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryHead raw (triple x y state))) := by
  apply compositionValue headCode (fun _ : Fin 1 => .projection 2)
    raw (triple x y state) (Fin.cons state Fin.elim0) (consHead state raw result hc)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 (triple x y state)

theorem summaryVertexValue (x y state raw result vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryVertex vertex (triple x y state))) := by
  apply compositionValue InternalUnpair.left (fun _ : Fin 1 => summaryHead)
    vertex (triple x y state) (Fin.cons raw Fin.elim0) (pairLeft raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact summaryHeadValue x y state raw result hc

theorem summaryCertificateValue (x y state raw result vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryCertificate certificate (triple x y state))) := by
  apply compositionValue InternalUnpair.right (fun _ : Fin 1 => summaryHead)
    certificate (triple x y state) (Fin.cons raw Fin.elim0) (pairRight raw vertex certificate hp)
  intro i
  obtain rfl := Fin.eq_zero i
  exact summaryHeadValue x y state raw result hc

theorem summaryTailValue (x y state raw result : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result))) :
    Nonempty (Derivation body Gamma (programGraph summaryTail result (triple x y state))) := by
  apply compositionValue tailCode (fun _ : Fin 1 => .projection 2)
    result (triple x y state) (Fin.cons state Fin.elim0) (consTail state raw result hc)
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 (triple x y state)

theorem edgeAtSummaryValue (edge : Program 3) (x y state raw result vertex certificate out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (programGraph edge out (triple x vertex certificate)))) :
    Nonempty (Derivation body Gamma (programGraph (edgeAtSummary edge) out (triple x y state))) := by
  apply compositionValue edge (triple (.projection 0) summaryVertex summaryCertificate)
    out (triple x y state) (triple x vertex certificate) he
  intro i
  exact Fin.cases (projectionValue 0 (triple x y state))
    (Fin.cases (summaryVertexValue x y state raw result vertex certificate hp hc)
      (Fin.cases (summaryCertificateValue x y state raw result vertex certificate hp hc)
        (fun q => Fin.elim0 q))) i

theorem edgeAtSummaryRecover (edge : Program 3) (x y state raw result vertex certificate out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (programGraph (edgeAtSummary edge) out (triple x y state)))) :
    Nonempty (Derivation body Gamma (programGraph edge out (triple x vertex certificate))) := by
  apply compositionRecover edge (triple (.projection 0) summaryVertex summaryCertificate)
    out (triple x y state) (triple x vertex certificate) he
  intro i
  exact Fin.cases (projectionValue 0 (triple x y state))
    (Fin.cases (summaryVertexValue x y state raw result vertex certificate hp hc)
      (Fin.cases (summaryCertificateValue x y state raw result vertex certificate hp hc)
        (fun q => Fin.elim0 q))) i

theorem endpointsValue (out x y state : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.equalityTest out
      (Fin.cons x (Fin.cons y Fin.elim0))))) :
    Nonempty (Derivation body Gamma (programGraph endpointsEqual out (triple x y state))) := by
  apply compositionValue InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)) out
    (triple x y state) (Fin.cons x (Fin.cons y Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 0 (triple x y state))
    (Fin.cases (projectionValue 1 (triple x y state)) (fun q => Fin.elim0 q)) i

theorem endpointsRecover (out x y state : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph endpointsEqual out (triple x y state)))) :
    Nonempty (Derivation body Gamma (programGraph InternalEqualityTest.equalityTest out
      (Fin.cons x (Fin.cons y Fin.elim0)))) := by
  apply compositionRecover InternalEqualityTest.equalityTest
    (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)) out
    (triple x y state) (Fin.cons x (Fin.cons y Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 0 (triple x y state))
    (Fin.cases (projectionValue 1 (triple x y state)) (fun q => Fin.elim0 q)) i

theorem finishZeroValue (edge : Program 3) (positive : Bool) (out x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (emptyFinish positive) out (triple x y z)))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive out x y z)) :=
  zeroBranchIntro (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    out (triple x y z) (projectionValue 2 (triple x y z)) h

theorem finishZeroRecover (edge : Program 3) (positive : Bool) (out x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (finishGraph edge positive out x y z))) :
    Nonempty (Derivation body Gamma (programGraph (emptyFinish positive) out (triple x y z))) :=
  zeroBranchElim (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    out (triple x y z) (projectionValue 2 (triple x y z)) h

/-- A nonempty summary accepts precisely its actual edge and its stored
suffix value equal to one. No Boolean range assumption is needed. -/
theorem finishConsAccept (edge : Program 3) (positive : Bool)
    (x y state raw result vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (he : Nonempty (Derivation body Gamma (edgeGraph edge x vertex certificate)))
    (hr : Nonempty (Derivation body Gamma (eqn result (suc z)))) :
    Nonempty (Derivation body Gamma (finishGraph edge positive (suc z) x y state)) := by
  have ha := edgeAtSummaryValue edge x y state raw result vertex certificate (suc z) hp hc he
  have hb := outputTransport summaryTail result (suc z) (triple x y state) hr
    (summaryTailValue x y state raw result hc)
  have hw := conjunctionAccept (edgeAtSummary edge) summaryTail (triple x y state) ha hb
  obtain ⟨hv⟩ := consDestruction state raw result hc
  exact nonzeroBranchIntro (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    (suc z) state (triple x y state) (projectionValue 2 (triple x y state))
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hv)⟩ hw

theorem finishConsRecover (edge : Program 3) (positive : Bool)
    (x y state raw result vertex certificate : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph raw vertex certificate)))
    (hc : Nonempty (Derivation body Gamma (consGraph state raw result)))
    (h : Nonempty (Derivation body Gamma (finishGraph edge positive (suc z) x y state))) :
    Nonempty (Derivation body Gamma (edgeGraph edge x vertex certificate ⊓ eqn result (suc z))) := by
  obtain ⟨hv⟩ := consDestruction state raw result hc
  have hw := nonzeroBranchElim (.projection 2) (emptyFinish positive) (nonemptyFinish edge)
    (suc z) state (triple x y state) (projectionValue 2 (triple x y state))
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hv)⟩ h
  obtain ⟨hab⟩ := conjunctionRecover (edgeAtSummary edge) summaryTail (triple x y state) hw
  obtain ⟨ha⟩ := edgeAtSummaryRecover edge x y state raw result vertex certificate (suc z)
    hp hc ⟨Derivation.conjunctionLeft hab⟩
  obtain ⟨hb⟩ := valueUnique summaryTail result (suc z) (triple x y state)
    (summaryTailValue x y state raw result hc) ⟨Derivation.conjunctionRight hab⟩
  exact ⟨Derivation.conjunctionIntroduction ha hb⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerFinishProof
