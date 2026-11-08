module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackReturnSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
def frameQ : Program 3 := visitOf (.projection 0)
def workQ : Program 3 := consOf frameQ (.projection 1)
def oldPairQ : Program 3 := pairOf workQ (.projection 2)
def leafQ (leaf : Program 1) : Program 3 := .composition leaf (fun _ : Fin 1 => .projection 0)
def resultQ (leaf : Program 1) : Program 3 := consOf (leafQ leaf) (.projection 2)
def newPairQ (leaf : Program 1) : Program 3 := pairOf (.projection 1) (resultQ leaf)
def newStateQ (leaf : Program 1) : Program 3 := liveOf (.projection 1) (resultQ leaf)
def queries (leaf : Program 1) : Fin 7 → Program 3 :=
  ![frameQ,workQ,oldPairQ,leafQ leaf,resultQ leaf,newPairQ leaf,newStateQ leaf]

theorem returnFromQueries (leaf : Program 1) (value work results : OTerm α) (ys : Fin 7 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries leaf i) (ys i)
      (Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (graph1 leaf (ys 3) value)) ∧
    Nonempty (Derivation body Gamma (graph3 returnState (ys 6) (ys 3) work results)) := by
  let xs : Fin 3 → OTerm α := Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0))
  have hl := unaryRecover leaf (.projection 0) (ys 3) value xs (hq 3) (projectionValue 0 xs)
  have hr := binaryRecover InternalListCodec.consCode (leafQ leaf) (.projection 2)
    (ys 4) (ys 3) results xs (hq 4) (hq 3) (projectionValue 2 xs)
  have hi := binaryRecover InternalPairing.pairing (.projection 1) (resultQ leaf)
    (ys 5) work (ys 4) xs (hq 5) (projectionValue 1 xs) (hq 4)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) (newPairQ leaf)
    (ys 6) (suc z) (ys 5) xs (hq 6) (InternalLessThanSupportProof.oneConstantValue xs) (hq 5)
  let rs : Fin 3 → OTerm α := Fin.cons (ys 3) (Fin.cons work (Fin.cons results Fin.elim0))
  have hr' := binaryValue InternalListCodec.consCode (.projection 0) (.projection 2)
    (ys 4) (ys 3) results rs hr (projectionValue 0 rs) (projectionValue 2 rs)
  have hi' := binaryValue InternalPairing.pairing (.projection 1) (consOf (.projection 0) (.projection 2))
    (ys 5) work (ys 4) rs hi (projectionValue 1 rs) hr'
  exact ⟨hl,binaryValue InternalPairing.pairing _ _ (ys 6) (suc z) (ys 5) rs ho
    (InternalLessThanSupportProof.oneConstantValue rs) hi'⟩

theorem transitionFromQueries (guard leaf : Program 1) (combine : Program 4)
    (value work results state : OTerm α) (ys : Fin 7 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value work results)))
    (hg : Nonempty (Derivation body Gamma (graph1 (openGuard guard) z value)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries leaf i) (ys i)
      (Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) (ys 6) state)) := by
  let xs : Fin 3 → OTerm α := Fin.cons value (Fin.cons work (Fin.cons results Fin.elim0))
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hf := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 3) (.projection 0)
    (ys 0) z value xs (hq 0) (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  have hw := binaryRecover InternalListCodec.consCode frameQ (.projection 1)
    (ys 1) (ys 0) work xs (hq 1) (hq 0) (projectionValue 1 xs)
  have hi := binaryRecover InternalPairing.pairing workQ (.projection 2)
    (ys 2) (ys 1) results xs (hq 2) (hq 1) (projectionValue 2 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) oldPairQ
    state (suc z) (ys 2) xs hs (InternalLessThanSupportProof.oneConstantValue xs) (hq 2)
  have hstatus := pairLeft state (suc z) (ys 2) ho
  have hinner := pairRight state (suc z) (ys 2) ho
  have hwork := unaryValue InternalUnpair.left InternalUnpair.right (ys 1) (ys 2) ss
    (pairLeft (ys 2) (ys 1) results hi) hinner
  have hresults := unaryValue InternalUnpair.right InternalUnpair.right results (ys 2) ss
    (pairRight (ys 2) (ys 1) results hi) hinner
  have hd := InternalListCodecSupportProof.consDestruction (ys 1) (ys 0) work hw
  have hframe := unaryValue InternalListCodec.headCode InternalApplicationResultStack.work
    (ys 0) (ys 1) ss (andLeft hd) hwork
  have hrest := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.work
    work (ys 1) ss (andLeft (andRight hd)) hwork
  have htag := unaryValue InternalUnpair.left currentFrame z (ys 0) ss
    (pairLeft (ys 0) z value hf) hframe
  have hvalue := unaryValue InternalUnpair.right currentFrame value (ys 0) ss
    (pairRight (ys 0) z value hf) hframe
  have hleaf := unaryValue leaf currentValue (ys 3) value ss
    ((returnFromQueries leaf value work results ys hq).1) hvalue
  have hr := binaryRecover InternalListCodec.consCode (leafQ leaf) (.projection 2)
    (ys 4) (ys 3) results xs (hq 4) (hq 3) (projectionValue 2 xs)
  have hnp := binaryRecover InternalPairing.pairing (.projection 1) (resultQ leaf)
    (ys 5) work (ys 4) xs (hq 5) (projectionValue 1 xs) (hq 4)
  have hns := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) (newPairQ leaf)
    (ys 6) (suc z) (ys 5) xs (hq 6) (InternalLessThanSupportProof.oneConstantValue xs) (hq 5)
  have hrl := binaryValue InternalListCodec.consCode
    (.composition leaf (fun _ : Fin 1 => currentValue)) InternalApplicationResultStack.results
    (ys 4) (ys 3) results ss hr hleaf hresults
  have hnewpair := binaryValue InternalPairing.pairing rest
    (consOf (.composition leaf (fun _ : Fin 1 => currentValue)) InternalApplicationResultStack.results)
    (ys 5) work (ys 4) ss hnp hrest hrl
  have hreturned : Nonempty (Derivation body Gamma (graph1 (leafReturned leaf) (ys 6) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 6) (suc z) (ys 5) ss hns
      (InternalLessThanSupportProof.oneConstantValue ss) hnewpair
  have hstatusOne := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  have htagZero := sameAccept frameTag (InternalAcceptance.constantZero 1) z ss htag
    (InternalLessThanSupportProof.zeroConstantValue ss)
  have hopen := unaryValue (openGuard guard) currentValue z value ss hg hvalue
  apply successorBranchIntro _ _ _ (ys 6) z ss hstatusOne
  apply nonzeroBranchIntro _ _ _ (ys 6) (ys 1) ss hwork (by simpa only [equalEqn] using (andRight (andRight hd)))
  apply successorBranchIntro _ _ _ (ys 6) z ss htagZero
  exact zeroBranchIntro _ _ _ (ys 6) ss hopen hreturned
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafSupportProof
