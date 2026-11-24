module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountEffectProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseHeadCountProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchQueryCasesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseReportSuppliersProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSupportProof (binaryRecover)
open InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof (projectionValue headTransport valueUnique)
open InternalTagArithmeticSupportProof (symm trans addZero)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel emb bindEmbedding liftBind varBind)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalBetaExtensionSyntaxProof (impRename)
open InternalOriginalOrderSyntaxProof (addRelabel)
open NumberedWindowInternalScratchQueryCasesProof (queryCases notRename)
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalLiteralScratchEraseCountTransportProof (liftEffect delta)
open NumberedWindowInternalLiteralScratchEraseCountEffectProof (countEffect countEffectRename countEffectSubst applyAt introduce)
open NumberedWindowInternalLiteralScratchEraseHeadCountProof (atHeadCounts)

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

private def queries : Fin 2 → Program 3 :=
  ![.composition entryCount ![.projection 0,.projection 2],
    .composition entryCount ![.projection 1,.projection 2] ]

private theorem recover (left right query : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![left,right,query]))) :
    Nonempty (Derivation body Delta (graph2 entryCount (ys 0) left query)) ∧
    Nonempty (Derivation body Delta (graph2 entryCount (ys 1) right query)) := by
  constructor
  · exact binaryRecover entryCount (.projection 0) (.projection 2) (ys 0) left query ![left,right,query]
      (hq 0) (projectionValue 0 ![left,right,query]) (projectionValue 2 ![left,right,query])
  · exact binaryRecover entryCount (.projection 1) (.projection 2) (ys 1) right query ![left,right,query]
      (hq 1) (projectionValue 1 ![left,right,query]) (projectionValue 2 ![left,right,query])
theorem atQuery (left right head tail rest needle query lc rc bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 entryCount lc left query)))
    (hr : Nonempty (Derivation body Delta (graph2 entryCount rc right query))) :
    Nonempty (Derivation body Delta
      (((eqn needle query).imp (eqn lc (OrdinaryArithmetic.addTerm rc bit))) ⊓
       ((eqn needle query).not.imp (eqn lc rc)))) := by
  apply queryCases queries ![tail,rest,query] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![tail,rest,query] i).relabel j) = ![tail.relabel j,rest.relabel j,query.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) i
  rw [hx] at hq
  obtain ⟨ht,hs⟩ := recover (tail.relabel j) (rest.relabel j) (query.relabel j) ys hq
  simp only [conjunctionRename,impRename,notRename,eqnRelabel,addRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hhj := renameInto h j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename] at hlcj hrcj hlj hrj
  rw [countEffectRename] at hhj
  have d := applyAt (tail.relabel j) (needle.relabel j) (rest.relabel j) (bit.relabel j)
    (query.relabel j) (ys 0) (ys 1) hhj ht hs
  exact liftEffect (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j)
    (rest.relabel j) (needle.relabel j) (query.relabel j) (lc.relabel j) (rc.relabel j)
    (ys 0) (ys 1) (bit.relabel j) hlcj hrcj hlj hrj ht hs d

theorem keep (left right head tail rest needle bit : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (hrc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode right head rest)))
    (h : Nonempty (Derivation body Delta (countEffect tail needle rest bit))) :
    Nonempty (Derivation body Delta (countEffect left needle right bit)) := by
  apply introduce left needle right bit
  intro beta j Theta query lc rc hj hl hr
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hhj := renameInto h j Theta hj
  rw [graph2Rename] at hlcj hrcj
  rw [countEffectRename] at hhj
  exact atQuery (left.relabel j) (right.relabel j) (head.relabel j) (tail.relabel j)
    (rest.relabel j) (needle.relabel j) query lc rc (bit.relabel j) hlcj hrcj hhj hl hr

/-- Quantifies the exact matching-head count effect over all original queries. -/
theorem headReport (raw head tail needle remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (hrem : Nonempty (Derivation body Delta (eqn remaining tail))) :
    Nonempty (Derivation body Delta (countEffect raw needle remaining (suc z))) := by
  apply introduce raw needle remaining (suc z)
  intro beta j Theta query lc rc keep hl hr
  have hcj := renameInto hc j Theta keep
  have hej := renameInto he j Theta keep
  have hrj := renameInto hrem j Theta keep
  rw [graph2Rename] at hcj
  rw [eqnRelabel] at hej hrj
  simp only [sucRelabel,zRelabel]
  exact atHeadCounts (raw.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (remaining.relabel j) query lc rc hcj hej hrj hl hr

/-- A real zero result returns the same raw tape, so all literal counts are unchanged. -/
theorem zeroReport (raw needle rest : OTerm alpha)
    (same : Nonempty (Derivation body Delta (eqn rest raw))) :
    Nonempty (Derivation body Delta (countEffect raw needle rest z)) := by
  apply introduce raw needle rest z
  intro beta j Theta query lc rc keep hl hr
  have eq := renameInto same j Theta keep
  rw [eqnRelabel] at eq
  have h := headTransport entryCount rc (rest.relabel j) (raw.relabel j) (Fin.cons query Fin.elim0) eq hr
  obtain ⟨sameCount⟩ := valueUnique entryCount lc rc ![raw.relabel j,query] hl h
  simp only [zRelabel]
  unfold delta
  let E := eqn (needle.relabel j) query
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction
      (InternalBetaTotalityProof.addHyp (trans sameCount (symm (addZero rc))) E))
    (Derivation.implicationIntroduction (InternalBetaTotalityProof.addHyp sameCount E.not))⟩

/-- Transfer a complete report only along actual object bit equality. -/
theorem bitReport (raw needle rest oldBit actualBit : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn oldBit actualBit)))
    (report : Nonempty (Derivation body Delta (countEffect raw needle rest oldBit))) :
    Nonempty (Derivation body Delta (countEffect raw needle rest actualBit)) := by
  obtain ⟨e⟩ := he
  obtain ⟨r⟩ := report
  have transport := Derivation.equalityElimination
    (countEffect (raw.relabel Sum.inl) (needle.relabel Sum.inl) (rest.relabel Sum.inl) (.var (.inr 0)))
    (emb oldBit) (emb actualBit) e
  simp only [instantiate,bindEmbedding,countEffectSubst,liftBind,varBind] at transport
  exact ⟨transport r⟩

#print axioms zeroReport
#print axioms bitReport
#print axioms keep
#print axioms headReport
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseReportSuppliersProof
