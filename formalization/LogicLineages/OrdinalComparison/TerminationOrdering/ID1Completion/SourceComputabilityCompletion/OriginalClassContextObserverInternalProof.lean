module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalActiveClassKernelEqualityProof (keyGraph keyTransfer)
open OriginalObservedClassProof (sameKnownRight)
open OriginalClassContextObserver OriginalClassContextObserverTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The reverse direction uses the SAME literal equality-test graph and an
actual candidate output. It does not infer equality from native evaluation. -/
theorem keyTransferBack (R : Program 2) (seed candidate parameter value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (keyGraph R seed candidate parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 R value candidate parameter))) :
    Nonempty (Derivation body Delta (graph2 R value seed parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  have hc' := binaryValue R (.projection 1) (.projection 2) value candidate parameter xs
    hc (projectionValue 1 xs) (projectionValue 2 xs)
  have hs := sameKnownRight (.composition R ![.projection 0,.projection 2])
    (.composition R ![.projection 1,.projection 2]) value xs hk hc'
  exact binaryRecover R (.projection 0) (.projection 2) value seed parameter xs
    hs (projectionValue 0 xs) (projectionValue 2 xs)

theorem keyOutputIff (R : Program 2) (seed candidate parameter value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (keyGraph R seed candidate parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 R value seed parameter).iff (graph2 R value candidate parameter))) := by
  let A := graph2 R value seed parameter
  let B := graph2 R value candidate parameter
  obtain ⟨hf⟩ := keyTransfer R seed candidate parameter value (withHyp hk A)
    (show Nonempty (Derivation body (A :: Delta) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := keyTransferBack R seed candidate parameter value (withHyp hk B)
    (show Nonempty (Derivation body (B :: Delta) B) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- Nonempty-context and activation branch graphs expose the actual two
observer tests. No class preservation of the full canonical fold is claimed. -/
theorem observerHits (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3)
    (seed candidate parameter gamma tail : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hg : Nonempty (Derivation body Delta
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (hn : Nonempty (Derivation body Delta (equal gamma (OrdinaryArithmetic.succTerm tail))))
    (hh : Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed candidate parameter))) :
    Nonempty (Derivation body Delta
      (keyGraph (erasedKey p.base.oldRepresentative) seed candidate parameter ⊓
        keyGraph erasedRank seed candidate parameter)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons candidate (Fin.cons parameter Fin.elim0))
  let A : Program 3 := .composition (OriginalActiveObservedClass.activation p H G W)
    ![.projection 0,.projection 2]
  let B := InternalAcceptance.branch A P
    (InternalAcceptance.conjunction P (observerTest p.base.oldRepresentative))
  have he : Nonempty (Derivation body Delta (eqn gamma (suc tail))) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using hn
  have hgs := outputTransport InternalUnpair.right gamma (suc tail)
    (Fin.cons parameter Fin.elim0) he hg
  have hc := unaryValue InternalUnpair.right (.projection 2) (suc tail) parameter xs
    hgs (projectionValue 2 xs)
  have hbranch := successorBranchElim (rightOf (.projection 2)) P B (suc z) tail xs hc hh
  have hac := binaryValue (OriginalActiveObservedClass.activation p H G W)
    (.projection 0) (.projection 2) (suc z) seed parameter xs ha
    (projectionValue 0 xs) (projectionValue 2 xs)
  have hconj := successorBranchElim A P
    (InternalAcceptance.conjunction P (observerTest p.base.oldRepresentative))
    (suc z) z xs hac hbranch
  have hob := andRight (conjunctionRecover P (observerTest p.base.oldRepresentative) xs hconj)
  exact conjunctionRecover (OriginalActiveClassKernel.keyTest (erasedKey p.base.oldRepresentative))
    (OriginalActiveClassKernel.keyTest erasedRank) xs hob

theorem actualOriginalClassContextObserverHit : ActualOriginalClassContextObserverHit := by
  intro p H G W P body alpha Delta seed candidate parameter gamma tail key rank
  let A := graph2 (OriginalActiveObservedClass.activation p H G W)
      InternalOriginalStepGuard.one seed parameter ⊓
    (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
      ((equal gamma (OrdinaryArithmetic.succTerm tail)) ⊓
        OriginalTransparentMinimum.graph3 (classTest p H G W P)
          InternalOriginalStepGuard.one seed candidate parameter))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ho := observerHits p H G W P seed candidate parameter gamma tail
    (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  obtain ⟨hout⟩ := andIntro
    (keyOutputIff (erasedKey p.base.oldRepresentative) seed candidate parameter key (andLeft ho))
    (keyOutputIff erasedRank seed candidate parameter rank (andRight ho))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
