module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalConstructorShape OriginalConstructorShapeSyntaxProof
open OriginalConstructorShapeApplicationProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Original pair projections recover both stored root fields from a mark.
The queried actual field outputs are identified by original functionality. -/
theorem markFields (value rootTag domain input : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value rootTag domain)))
    (hm : Nonempty (Derivation body Delta (markGraph value input))) :
    Nonempty (Derivation body Delta
      (tagGraph rootTag input ⊓ graph1 applicationDomain domain input)) := by
  let qs : Fin 2 → Program 1 := ![tag,applicationDomain]
  apply queryCases qs (Fin.cons input Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [conjunctionRename,tagGraphRename,graph1Rename]
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  rw [graph2Rename] at hp'
  rw [markGraphRename] at hm'
  simp only [consTermRename,emptyRename] at hq
  have hactual := binaryRecover InternalPairing.pairing tag applicationDomain
    (value.relabel j) (ys 0) (ys 1) (Fin.cons (input.relabel j) Fin.elim0) hm' (hq 0) (hq 1)
  have htagEq := valueUnique InternalUnpair.left (ys 0) (rootTag.relabel j)
    (Fin.cons (value.relabel j) Fin.elim0)
    (pairLeft (value.relabel j) (ys 0) (ys 1) hactual)
    (pairLeft (value.relabel j) (rootTag.relabel j) (domain.relabel j) hp')
  have hdomainEq := valueUnique InternalUnpair.right (ys 1) (domain.relabel j)
    (Fin.cons (value.relabel j) Fin.elim0)
    (pairRight (value.relabel j) (ys 0) (ys 1) hactual)
    (pairRight (value.relabel j) (rootTag.relabel j) (domain.relabel j) hp')
  exact andIntro
    (outputTransport tag (ys 0) (rootTag.relabel j) (Fin.cons (input.relabel j) Fin.elim0) htagEq (hq 0))
    (outputTransport applicationDomain (ys 1) (domain.relabel j)
      (Fin.cons (input.relabel j) Fin.elim0) hdomainEq (hq 1))

/-- A common actual mark transports every symbolic constructor tag. The
second stored field is internally bound, with no supplied mark decomposition. -/
theorem sharedTag (value source target rootTag : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (markGraph value source)))
    (ht : Nonempty (Derivation body Delta (markGraph value target)))
    (htag : Nonempty (Derivation body Delta (tagGraph rootTag source))) :
    Nonempty (Derivation body Delta (tagGraph rootTag target)) := by
  apply programCases applicationDomain (Fin.cons source Fin.elim0) _
  intro beta j Theta domain hj hd
  rw [tagGraphRename]
  have hs' := renameInto hs j Theta hj
  have ht' := renameInto ht j Theta hj
  have htag' := renameInto htag j Theta hj
  rw [markGraphRename] at hs' ht'
  rw [tagGraphRename] at htag'
  simp only [consTermRename,emptyRename] at hd
  have hp := binaryRecover InternalPairing.pairing tag applicationDomain
    (value.relabel j) (rootTag.relabel j) domain (Fin.cons (source.relabel j) Fin.elim0)
    hs' htag' hd
  exact andLeft (markFields (value.relabel j) (rootTag.relabel j) domain (target.relabel j) hp ht')

/-- At tag two, the stored domain is the actual original appDomain. The
original branch equation recovers it after both pair fields are transported. -/
theorem sharedApplicationShape (value source target domain : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (markGraph value source)))
    (ht : Nonempty (Derivation body Delta (markGraph value target)))
    (hshape : Nonempty (Derivation body Delta (applicationShape domain source))) :
    Nonempty (Derivation body Delta (applicationShape domain target)) := by
  have hpair := applicationMarkForward value domain source hshape hs
  have hf := markFields value positionTerm domain target hpair ht
  let xs : Fin 1 → OTerm alpha := Fin.cons target Fin.elim0
  have htest := sameAccept tag (two 1) positionTerm xs (andLeft hf) (twoValue xs)
  have hdomain := successorBranchElim (InternalApplicationStepPeel.same tag (two 1))
    (InternalAcceptance.constantZero 1) (InternalApplicationStepPeel.appDomain (.projection 0))
    domain z xs htest (andRight hf)
  exact andIntro (andLeft hf) hdomain

theorem sharedTagIff (value source target rootTag : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (markGraph value source)))
    (ht : Nonempty (Derivation body Delta (markGraph value target))) :
    Nonempty (Derivation body Delta ((tagGraph rootTag source).iff (tagGraph rootTag target))) := by
  let P := tagGraph rootTag source
  let Q := tagGraph rootTag target
  obtain ⟨hf⟩ := sharedTag value source target rootTag (withHyp hs P) (withHyp ht P)
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := sharedTag value target source rootTag (withHyp ht Q) (withHyp hs Q)
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem sharedApplicationIff (value source target domain : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (markGraph value source)))
    (ht : Nonempty (Derivation body Delta (markGraph value target))) :
    Nonempty (Derivation body Delta
      ((applicationShape domain source).iff (applicationShape domain target))) := by
  let P := applicationShape domain source
  let Q := applicationShape domain target
  obtain ⟨hf⟩ := sharedApplicationShape value source target domain (withHyp hs P) (withHyp ht P)
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := sharedApplicationShape value target source domain (withHyp ht Q) (withHyp hs Q)
    (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem fieldsIffRename {beta : Type} (out input value domain : OTerm alpha) (j : alpha → beta) :
    (((tagGraph value out).iff (tagGraph value input)) ⊓
      ((applicationShape domain out).iff (applicationShape domain input))).relabel j =
    ((tagGraph (value.relabel j) (out.relabel j)).iff (tagGraph (value.relabel j) (input.relabel j))) ⊓
      ((applicationShape (domain.relabel j) (out.relabel j)).iff
        (applicationShape (domain.relabel j) (input.relabel j))) := by
  change (((tagGraph value out).relabel j).iff ((tagGraph value input).relabel j)) ⊓
    (((applicationShape domain out).relabel j).iff ((applicationShape domain input).relabel j)) = _
  rw [tagGraphRename,tagGraphRename,applicationShapeRename,applicationShapeRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeRootFieldsProof
