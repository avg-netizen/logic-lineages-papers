module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalParameterizedApplicationResultStack InternalParameterizedApplicationResultStackWiringProof
open InternalParameterizedApplicationResultStackSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionFrameSupportProof
open InternalApplicationResultStackCompositionFrameConstructorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Only two original constructor subgraphs are needed to recover the root
tag test. No source-validity, decoder, or external evaluation premise occurs. -/
theorem rootTagAccept (d e fp ap value : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap))) :
    Nonempty (Derivation body Gamma (graph1
      (InternalApplicationStepPeel.same
        (InternalApplicationStepPeel.constructorTag (.projection 0)) (two 1)) (suc z) value)) := by
  let bodyQ : Program 4 := pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))
  let nodeQ : Program 4 := pairOf (two 4) bodyQ
  let qs : Fin 2 → Program 4 := ![bodyQ,nodeQ]
  let xs : Fin 4 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  simp only [graph1Rename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Delta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let ts : Fin 4 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  let vs : Fin 1 → OTerm β := Fin.cons (value.relabel j) Fin.elim0
  have hn := binaryRecover InternalPairing.pairing (two 4) bodyQ
    (ys 1) positionTerm (ys 0) ts (hq 1) (twoValue ts) (hq 0)
  have ho := binaryRecover InternalPairing.pairing (.projection 1) nodeQ
    (value.relabel j) (e.relabel j) (ys 1) ts hp' (projectionValue 1 ts) (hq 1)
  have hv := unaryValue InternalUnpair.right (.projection 0) (ys 1) (value.relabel j) vs
    (pairRight (value.relabel j) (e.relabel j) (ys 1) ho) (projectionValue 0 vs)
  have ht := unaryValue InternalUnpair.left (rightOf (.projection 0)) positionTerm (ys 1) vs
    (pairLeft (ys 1) positionTerm (ys 0) hn) hv
  exact sameAccept _ (two 1) positionTerm vs ht (twoValue vs)

/-- Reuse the original unary opening theorem to identify the expanded
state. Only the small state/control envelope is lifted to the binary AST. -/
theorem expandedAt (guard leaf : Program 2) (combine : Program 5)
    (d e fp ap value tail results state stack frame out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) value parameter)))
    (he : Nonempty (Derivation body Gamma (graph1 expanded out state))) :
    Nonempty (Derivation body Gamma
      (graph2 (transitionP guard leaf combine) out state parameter ⊓
        graph6 expandedState out d e fp ap tail results)) := by
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let vs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let vp : Fin 2 → OTerm α := Fin.cons value (Fin.cons parameter Fin.elim0)
  have fields := currentFields state stack results frame tail z value hs hc hf
  have htag := andLeft (andRight (andRight fields))
  have hvalue := andRight (andRight (andRight fields))
  have hframe := sameAccept frameTag (InternalAcceptance.constantZero 1) z ss htag (constantZeroValue ss)
  have hroot := rootTagAccept d e fp ap value hp
  have hopen : Nonempty (Derivation body Gamma (graph2 (openGuardP guard) (suc z) value parameter)) :=
    conjunctionAccept _ guard vp (liftValue _ (suc z) value parameter hroot) hg
  have hopenAt : Nonempty (Derivation body Gamma
      (graph2 (wireP (openGuardP guard) ![currentValue]) (suc z) state parameter)) := by
    apply wireValue _ _ (suc z) state parameter (Fin.cons value Fin.elim0)
    · simpa only [appendParameterOne] using hopen
    · intro i
      obtain rfl := Fin.eq_zero i
      exact hvalue
  have hnew : Nonempty (Derivation body Gamma
      (graph2 (transitionP guard leaf combine) out state parameter)) := by
    apply InternalParameterizedApplicationResultStackReturnSupportProof.liveInner
      guard leaf combine state stack results frame tail out parameter hs hc
    apply successorBranchIntro _ _ _ out z xs (liftValue _ (suc z) state parameter hframe)
    exact successorBranchIntro _ _ _ out z xs hopenAt (liftValue expanded out state parameter he)
  have hone : Nonempty (Derivation body Gamma (graph1 (InternalLessThan.constantOne 1) (suc z) value)) :=
    InternalLessThanSupportProof.oneConstantValue vs
  have hopenOld : Nonempty (Derivation body Gamma
      (graph1 (openGuard (InternalLessThan.constantOne 1)) (suc z) value)) :=
    conjunctionAccept _ _ vs hroot hone
  have hold : Nonempty (Derivation body Gamma
      (graph1 (transition (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
        (InternalAcceptance.constantZero 4)) out state)) := by
    apply InternalApplicationResultStackCompositionFrameSupportProof.liveInner
      (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
      (InternalAcceptance.constantZero 4) state stack results frame tail out hs hc
    apply successorBranchIntro _ _ _ out z ss hframe
    exact successorBranchIntro _ _ _ out z ss
      (unaryValue (openGuard (InternalLessThan.constantOne 1)) currentValue (suc z) value ss hopenOld hvalue) he
  exact andIntro hnew
    (InternalApplicationResultStackVisitProof.visitForward
      (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1)
      (InternalAcceptance.constantZero 4) d e fp ap value tail results state out hp
      (visitStateAt state stack results frame value tail hs hc hf) hone hold)

theorem visitAt (guard leaf : Program 2) (combine : Program 5)
    (d e fp ap value tail results state out parameter : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph4 packedApplication value d e fp ap)))
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (hg : Nonempty (Derivation body Gamma (graph2 guard (suc z) value parameter)))
    (he : Nonempty (Derivation body Gamma (graph1 expanded out state))) :
    Nonempty (Derivation body Gamma
      (graph2 (transitionP guard leaf combine) out state parameter ⊓
        graph6 expandedState out d e fp ap tail results)) := by
  apply InternalParameterizedApplicationResultStackReturnSupportProof.visitStateCases state value tail results _ hs
  intro β j Delta frame stack hj hl hc hf
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,
    InternalApplicationResultStackVisitSupportProof.graph6Rename]
  have hp' := renameInto hp j Delta hj
  have hg' := renameInto hg j Delta hj
  have he' := renameInto he j Delta hj
  simp only [graph4Rename] at hp'
  simp only [graph2Rename,sucRelabel,zRelabel] at hg'
  simp only [graph1Rename] at he'
  exact expandedAt guard leaf combine (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (value.relabel j) (tail.relabel j) (results.relabel j) (state.relabel j) stack frame
    (out.relabel j) (parameter.relabel j) hp' hl hc hf hg' he'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitSupportProof
