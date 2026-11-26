module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedMinimumInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open OriginalClassContextAllPositionSelection OriginalClassContextAllPositionSelectionTargets
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

theorem middleTransport (Q : Program 3) (value cutoff seed out parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn seed out)))
    (hv : Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 Q value cutoff seed parameter))) :
    Nonempty (Derivation body Delta (OriginalTransparentMinimum.graph3 Q value cutoff out parameter)) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 3 Delta
    (OrdinaryArithmetic.graphFormula Q) value
    (Fin.cons cutoff (Fin.cons seed (Fin.cons parameter Fin.elim0)))
    (Fin.cons cutoff (Fin.cons out (Fin.cons parameter Fin.elim0))) _ hv
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact ⟨InternalTagArithmeticSupportProof.refl cutoff⟩
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact he
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact ⟨InternalTagArithmeticSupportProof.refl parameter⟩

theorem observationOfEqual (Q : Program 3) (value cutoff seed out parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out seed))) :
    Nonempty (Derivation body Delta
      ((OriginalTransparentMinimum.graph3 Q value cutoff seed parameter).iff
        (OriginalTransparentMinimum.graph3 Q value cutoff out parameter))) := by
  let A := OriginalTransparentMinimum.graph3 Q value cutoff seed parameter
  let B := OriginalTransparentMinimum.graph3 Q value cutoff out parameter
  obtain ⟨heA⟩ := withHyp he A
  obtain ⟨hf⟩ := middleTransport Q value cutoff seed out parameter
    ⟨InternalTagArithmeticSupportProof.symm heA⟩
    (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := middleTransport Q value cutoff out seed parameter (withHyp he B)
    (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem outputAt (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (seed out parameter gamma count cutoff value : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W seed parameter)))
    (hg : Nonempty (Derivation body Delta (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0))))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
    (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (inputs p H G W P).base.oldRepresentative out seed parameter))) :
    Nonempty (Derivation body Delta
      ((OriginalTransparentMinimum.graph3
        (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        value cutoff seed parameter).iff
       (OriginalTransparentMinimum.graph3
        (OriginalClassContextAllPositionObserver.positionObservation p.base.oldRepresentative)
        value cutoff out parameter))) := by
  let E := classTest p H G W P
  obtain ⟨hm⟩ := OriginalActiveObservedMinimumInternalProof.actualOriginalActiveObservedMinimumInternalMinimum
    p H G W E body alpha Delta out seed parameter seed
  obtain ⟨hhyp⟩ := andIntro (andLeft hd) (andIntro (andRight hd) hr)
  have hhit := andLeft (andRight (show Nonempty (Derivation body Delta _) from
    ⟨Derivation.implicationElimination hm hhyp⟩))
  apply formulaCases (eqn out seed)
  · exact observationOfEqual _ value cutoff seed out parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have he := observerClassOfNonreflexive p H G W P seed out parameter
      (withHyp (andRight hd) (eqn out seed).not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hhit (eqn out seed).not)
    obtain ⟨hintro⟩ := OriginalClassContextAllPositionInternalProof.actualHit
      p H G W (OriginalActiveClassKernel.classTest p H G W P) body alpha
      ((eqn out seed).not :: Delta) seed out parameter gamma count cutoff value
    obtain ⟨hpre⟩ := andIntro (withHyp (andRight hd) (eqn out seed).not)
      (andIntro (withHyp hg (eqn out seed).not)
        (andIntro (withHyp hl (eqn out seed).not) (andIntro (withHyp hb (eqn out seed).not) he)))
    exact ⟨Derivation.implicationElimination hintro hpre⟩

theorem actualOutput : ActualOutput := by
  intro p H G W P body alpha Delta seed out parameter gamma count cutoff value
  let A := OriginalActiveClassKernel.Domain p H G W seed parameter ⊓
    (programGraph InternalUnpair.right gamma (Fin.cons parameter Fin.elim0) ⊓
      (OriginalContextInsertion.lengthGraph count gamma ⊓
        (OriginalContextInsertion.Below cutoff count ⊓ graph2 (inputs p H G W P).base.oldRepresentative out seed parameter)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := outputAt p H G W P seed out parameter gamma count cutoff value
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction ho⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionSelectionOutputProof
