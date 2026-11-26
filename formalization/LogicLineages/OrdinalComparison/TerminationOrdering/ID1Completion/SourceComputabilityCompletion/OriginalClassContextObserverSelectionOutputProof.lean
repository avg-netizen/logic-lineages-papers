module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalActiveClassKernelEqualityProof (keyOfEqual)
open OriginalClassContextObserverInternalProof (observerHits keyOutputIff)
open OriginalClassContextObserverSelection OriginalClassContextObserverSelectionTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the literal E hit from the outer rank-observed reflexive wrapper
in the genuinely nonreflexive branch. -/
theorem observerClassOfNonreflexive (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveObservedClass.activation p H G W) (suc z) seed parameter)))
    (hne : Nonempty (Derivation body Delta (eqn out seed).not))
    (hh : Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3
        (OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G)
          (OriginalActiveObservedClass.classTest p H G W
            OriginalRawSyntaxTransport.variableRankPackedRaw (classTest p H G W P)))
        (suc z) seed out parameter))) :
    Nonempty (Derivation body Delta
      (OriginalTransparentMinimum.graph3 (classTest p H G W P) (suc z) seed out parameter)) := by
  let E := classTest p H G W P
  let O := OriginalRawSyntaxTransport.variableRankPackedRaw
  let Q := OriginalActiveObservedClass.classTest p H G W O E
  let xs : Fin 3 → OTerm alpha := Fin.cons seed (Fin.cons out (Fin.cons parameter Fin.elim0))
  have hz := OriginalActiveClassKernelBranchProof.equalityControl z seed out parameter
    (OriginalVariableDecoderEqualityProof.equalityReject out seed hne)
  have hQ := zeroBranchElim
    (.composition InternalEqualityTest.equalityTest ![.projection 1,.projection 0])
    Q (.composition (OriginalTypedDecoder.target H G) ![.projection 0,.projection 2])
    (suc z) xs hz hh
  have hact := binaryValue (OriginalActiveObservedClass.activation p H G W)
    (.projection 0) (.projection 2) (suc z) seed parameter xs ha
    (projectionValue 0 xs) (projectionValue 2 xs)
  have ho := successorBranchElim
    (.composition (OriginalActiveObservedClass.activation p H G W) ![.projection 0,.projection 2])
    E (OriginalObservedClass.observed O E) (suc z) z xs hact hQ
  exact andLeft (conjunctionRecover E
    (InternalApplicationStepPeel.same (OriginalObservedClassProof.candidateQuery O)
      (OriginalObservedClassProof.seedQuery O)) xs ho)

/-- Both reflexive and nonreflexive actual minimum hits preserve the erased
observers. The reflexive branch is paid by actual equality graph transport. -/
theorem outputAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter gamma tail key rank : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hg : Nonempty (Derivation body Delta
      (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (hn : Nonempty (Derivation body Delta (equal gamma (OrdinaryArithmetic.succTerm tail))))
    (hr : Nonempty (Derivation body Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta
      (((graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
          key seed parameter).iff
        (graph2 (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
          key out parameter)) ⊓
        ((graph2 OriginalClassContextObserver.erasedRank rank seed parameter).iff
          (graph2 OriginalClassContextObserver.erasedRank rank out parameter)))) := by
  let E := classTest p H G W P
  obtain ⟨hm⟩ := OriginalActiveObservedMinimumInternalProof.actualOriginalActiveObservedMinimumInternalMinimum
    p H G W E body alpha Delta out seed parameter seed
  obtain ⟨hhyp⟩ := andIntro (andLeft hd) (andIntro (andRight hd) hr)
  have hhit := andLeft (andRight (show Nonempty (Derivation body Delta _) from
    ⟨Derivation.implicationElimination hm hhyp⟩))
  apply formulaCases (eqn out seed)
  · exact andIntro
      (keyOutputIff (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
        seed out parameter key
        (keyOfEqual _ seed out parameter ⟨Derivation.hypothesis List.mem_cons_self⟩))
      (keyOutputIff OriginalClassContextObserver.erasedRank seed out parameter rank
        (keyOfEqual _ seed out parameter ⟨Derivation.hypothesis List.mem_cons_self⟩))
  · have he := observerClassOfNonreflexive p H G W P seed out parameter
      (withHyp (andRight hd) (eqn out seed).not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hhit (eqn out seed).not)
    have ho := observerHits p H G W (OriginalActiveClassKernel.classTest p H G W P)
      seed out parameter gamma tail
      (withHyp (andRight hd) (eqn out seed).not) (withHyp hg (eqn out seed).not)
      (withHyp hn (eqn out seed).not) he
    exact andIntro
      (keyOutputIff (OriginalClassContextObserver.erasedKey p.base.oldRepresentative)
        seed out parameter key (andLeft ho))
      (keyOutputIff OriginalClassContextObserver.erasedRank seed out parameter rank (andRight ho))

theorem actualOriginalClassContextObserverOutput : ActualOriginalClassContextObserverOutput := by
  intro p H G W P body alpha Delta seed out parameter gamma tail key rank
  let A := OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
    (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
      ((equal gamma (OrdinaryArithmetic.succTerm tail)) ⊓
        graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := outputAt p H G W P seed out parameter gamma tail key rank
    (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverSelectionOutputProof
