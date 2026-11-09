module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalBetaTotalityProof (addHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityCompletion.BottomSpineMeasure (measure fold leaf combine)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem measureRecover (out value : OTerm α)
    (h : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph out value))) :
    Nonempty (Derivation body Gamma (graph2 fold out value z)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  exact compositionRecover fold ![.projection 0,InternalAcceptance.constantZero 1]
    out xs (Fin.cons value (Fin.cons z Fin.elim0)) h
    (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (constantZeroValue xs) (fun k => Fin.elim0 k)) i)

theorem measureValue (out value : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 fold out value z))) :
    Nonempty (Derivation body Gamma (BottomSpineMeasure.graph out value)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  exact compositionValue fold ![.projection 0,InternalAcceptance.constantZero 1]
    out xs (Fin.cons value (Fin.cons z Fin.elim0)) h
    (fun i => Fin.cases (projectionValue 0 xs)
      (Fin.cases (constantZeroValue xs) (fun k => Fin.elim0 k)) i)

theorem combineValue (d e f a parameter flag depth next out : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag f)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth f)))
    (hs : Nonempty (Derivation body Gamma (graph1 Program.succ next depth)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out flag next))) :
    Nonempty (Derivation body Gamma
      (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0))))))) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0))))
  have hleft := unaryValue InternalUnpair.left (.projection (2 : Fin 5)) flag f xs hl (projectionValue 2 xs)
  have hright := unaryValue InternalUnpair.right (.projection (2 : Fin 5)) depth f xs hr (projectionValue 2 xs)
  have hnext := unaryValue Program.succ (rightOf (.projection (2 : Fin 5))) next depth xs hs hright
  exact binaryValue InternalPairing.pairing (leftOf (.projection (2 : Fin 5)))
    (.composition Program.succ (fun _ : Fin 1 => rightOf (.projection (2 : Fin 5)))) out flag next xs hp hleft hnext

theorem combineRecover (d e f a parameter flag depth next out : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag f)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth f)))
    (hs : Nonempty (Derivation body Gamma (graph1 Program.succ next depth)))
    (hc : Nonempty (Derivation body Gamma
      (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out flag next)) := by
  let xs : Fin 5 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0))))
  have hleft := unaryValue InternalUnpair.left (.projection (2 : Fin 5)) flag f xs hl (projectionValue 2 xs)
  have hright := unaryValue InternalUnpair.right (.projection (2 : Fin 5)) depth f xs hr (projectionValue 2 xs)
  have hnext := unaryValue Program.succ (rightOf (.projection (2 : Fin 5))) next depth xs hs hright
  exact binaryRecover InternalPairing.pairing (leftOf (.projection (2 : Fin 5)))
    (.composition Program.succ (fun _ : Fin 1 => rightOf (.projection (2 : Fin 5)))) out flag next xs hc hleft hnext

def premises (arrow d e fp ap f a parent fm am flag depth next : OTerm α) : Formula α :=
  InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap f a parent ⊓
    (BottomSpineMeasure.graph fm f ⊓
      (BottomSpineMeasure.graph am a ⊓
        (graph1 InternalUnpair.left flag fm ⊓
          (graph1 InternalUnpair.right depth fm ⊓ graph1 Program.succ next depth))))

theorem forward (arrow d e fp ap f a parent fm am flag depth next out : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises arrow d e fp ap f a parent fm am flag depth next)))
    (hp : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph out parent))) :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out flag next)) := by
  have hc := andLeft h
  have hf := andLeft (andRight h)
  have ha := andLeft (andRight (andRight h))
  have hl := andLeft (andRight (andRight (andRight h)))
  have hr := andLeft (andRight (andRight (andRight (andRight h))))
  have hs := andRight (andRight (andRight (andRight (andRight h))))
  have hg := InternalLessThanSupportProof.oneConstantValue (body := body) (Gamma := Gamma) (Fin.cons parent (Fin.cons z Fin.elim0))
  have hcomb := InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationBackward
    (InternalLessThan.constantOne 2) leaf combine arrow d e fp ap f a parent fm am out z
    hc hg (measureRecover fm f hf) (measureRecover am a ha) (measureRecover out parent hp)
  exact combineRecover d e fm am z flag depth next out hl hr hs hcomb

theorem backward (arrow d e fp ap f a parent fm am flag depth next out : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises arrow d e fp ap f a parent fm am flag depth next)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out flag next))) :
    Nonempty (Derivation body Gamma (BottomSpineMeasure.graph out parent)) := by
  have hc := andLeft h
  have hf := andLeft (andRight h)
  have ha := andLeft (andRight (andRight h))
  have hl := andLeft (andRight (andRight (andRight h)))
  have hr := andLeft (andRight (andRight (andRight (andRight h))))
  have hs := andRight (andRight (andRight (andRight (andRight h))))
  have hg := InternalLessThanSupportProof.oneConstantValue (body := body) (Gamma := Gamma) (Fin.cons parent (Fin.cons z Fin.elim0))
  exact measureValue out parent
    (InternalParameterizedApplicationResultFoldTotalityConsumerProof.applicationForward
      (InternalLessThan.constantOne 2) leaf combine arrow d e fp ap f a parent fm am out z
      hc hg (measureRecover fm f hf) (measureRecover am a ha)
      (combineValue d e fm am z flag depth next out hl hr hs hp))

theorem actualParameterizedSpineMeasureApplication :
    BottomSpineMeasureTargets.ActualParameterizedSpineMeasureApplication := by
  intro body α Delta arrow d e fp ap f a parent fm am flag depth next out
  let H := premises arrow d e fp ap f a parent fm am flag depth next
  let P := BottomSpineMeasure.graph out parent
  let Q := graph2 InternalPairing.pairing out flag next
  have hh : Derivation body (H :: Delta) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hf⟩ := forward arrow d e fp ap f a parent fm am flag depth next out
    ⟨addHyp hh P⟩ (show Nonempty (Derivation body (P :: H :: Delta) P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := backward arrow d e fp ap f a parent fm am flag depth next out
    ⟨addHyp hh Q⟩ (show Nonempty (Derivation body (Q :: H :: Delta) Q) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
      (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureInternalProof
