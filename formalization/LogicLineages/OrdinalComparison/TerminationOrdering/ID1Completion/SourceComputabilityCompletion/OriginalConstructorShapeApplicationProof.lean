module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelComponentsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeApplicationMarkProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalConstructorShape OriginalConstructorShapeSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalApplicationStepPeelComponentsProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem iffFlip (P Q : Formula alpha)
    (h : Nonempty (Derivation body Delta (P.iff Q))) :
    Nonempty (Derivation body Delta (Q.iff P)) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionRight h) (Derivation.conjunctionLeft h)⟩

theorem iffCompose (P Q R : Formula alpha)
    (hp : Nonempty (Derivation body Delta (P.iff Q)))
    (hq : Nonempty (Derivation body Delta (Q.iff R))) :
    Nonempty (Derivation body Delta (P.iff R)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hq) P)
        (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft hp) P)
          (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hp) R)
        (Derivation.implicationElimination (addHyp (Derivation.conjunctionRight hq) R)
          (Derivation.hypothesis List.mem_cons_self))))⟩

/-- Actual tag and application-domain graphs recovered from the ORIGINAL
packed constructor at arbitrary raw payloads. -/
theorem packedFields (d e fp ap parent : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Delta (applicationShape d parent)) := by
  let children : Program 4 := pairOf (.projection 2) (.projection 3)
  let middle : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 3 → Program 4 := ![children,middle,node]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [applicationShapeRename]
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) children
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hpar := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 2) xx hp' (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs (.projection 0) (parent.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    (projectionValue 0 ss) hc hm hn hpar
  exact andIntro (andLeft (andRight fields)) (andLeft (andRight (andRight fields)))

theorem rawFields (d e fn arg parent : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg))) :
    Nonempty (Derivation body Delta (applicationShape d parent)) := by
  let qs : Fin 2 → Program 4 := ![rightOf (.projection 2),rightOf (.projection 3)]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fn (Fin.cons arg Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [applicationShapeRename]
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) Fin.elim0)))
  have hf := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (fn.relabel j) xx
    (hq 0) (projectionValue 2 xx)
  have ha := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (arg.relabel j) xx
    (hq 1) (projectionValue 3 xx)
  exact packedFields (d.relabel j) (e.relabel j) (ys 0) (ys 1) (parent.relabel j)
    (applicationForward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
      (ys 0) (ys 1) (parent.relabel j) hf ha hp')

theorem applicationDomainValue (d input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (applicationShape d input))) :
    Nonempty (Derivation body Delta (graph1 applicationDomain d input)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  exact successorBranchIntro (InternalApplicationStepPeel.same tag (two 1))
    (InternalAcceptance.constantZero 1) (InternalApplicationStepPeel.appDomain (.projection 0))
    d z xs (sameAccept tag (two 1) positionTerm xs (andLeft h) (twoValue xs)) (andRight h)

theorem applicationMarkForward (value d input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (applicationShape d input)))
    (hm : Nonempty (Derivation body Delta (markGraph value input))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value positionTerm d)) :=
  binaryRecover InternalPairing.pairing tag applicationDomain value positionTerm d
    (Fin.cons input Fin.elim0) hm (andLeft h) (applicationDomainValue d input h)

theorem applicationMarkBackward (value d input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (applicationShape d input)))
    (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value positionTerm d))) :
    Nonempty (Derivation body Delta (markGraph value input)) :=
  binaryValue InternalPairing.pairing tag applicationDomain value positionTerm d
    (Fin.cons input Fin.elim0) hm (andLeft h) (applicationDomainValue d input h)

theorem applicationMarkIff (value d input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (applicationShape d input))) :
    Nonempty (Derivation body Delta
      ((markGraph value input).iff (graph2 InternalPairing.pairing value positionTerm d))) := by
  let P := markGraph value input
  let Q := graph2 InternalPairing.pairing value positionTerm d
  obtain ⟨hf⟩ := applicationMarkForward value d input (withHyp h P)
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := applicationMarkBackward value d input (withHyp h Q)
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
