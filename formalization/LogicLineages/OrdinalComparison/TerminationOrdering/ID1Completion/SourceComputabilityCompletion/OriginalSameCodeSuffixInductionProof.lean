module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalParameterizedPathChecker InternalParameterizedPathCheckerSyntaxProof InternalParameterizedPathCheckerProof
open InternalListCodec InternalListCodecSupportProof InternalListInduction InternalListInductionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof SourceComputabilityFormulaSupportProof
open OriginalSameCodeSuffixInductionSyntaxProof OriginalSameCodeSuffixInductionCoreProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem zeroRow (edge : Program 4) (window : Program 1) :
    Nonempty (Derivation body Gamma (spineRow edge window z)) := by
  unfold spineRow
  apply actualFiniteUniversalIntroduction body alpha 3 Gamma
  let x : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let y : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := OriginalFunctionNeutrality.windowGraph window x parameter ⊓ positiveGraph edge x y z parameter
  let Delta := A :: Gamma.map (fun p => p.relabel Sum.inl)
  have hp : Nonempty (Derivation body Delta (positiveGraph edge x y z parameter)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := positiveNil (body := body) (Gamma := Delta) edge x y parameter
  have hf := Derivation.implicationElimination hn hp
  simpa only [spineBody,zRelabel,A,x,y,parameter,OriginalFunctionNeutrality.windowGraph,
    OriginalVariableRepresentative.windowGraph,positiveGraph,checkerGraph,graph4,
    InternalOriginalStepGuard.one,quadruple,z,suc] using
    (show Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (A.imp (OriginalSpineGuardLeaf.spineAccepted x y z parameter))) from
      ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩)

theorem consRow (data : Data) (window : Program 1) (oldStep : Program 4)
    (hguard : OriginalQuotientSpine.QuotientHasSpineGuard data window oldStep)
    (code raw tail : OTerm alpha)
    (hrow : Nonempty (Derivation body Gamma (spineRow (edgeChecker data oldStep) window tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code raw tail))) :
    Nonempty (Derivation body Gamma (spineRow (edgeChecker data oldStep) window code)) := by
  unfold spineRow
  apply actualFiniteUniversalIntroduction body alpha 3 Gamma
  let x : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let y : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let c := code.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let r := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let t := tail.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let A := OriginalFunctionNeutrality.windowGraph window x parameter ⊓
    positiveGraph (edgeChecker data oldStep) x y c parameter
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [spineRowRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  obtain ⟨d⟩ := consCore data window oldStep hguard x y c r t parameter hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩ hc'
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- The original full-language list-code induction composes literal guards.
The quotient supplier is explicit here and is discharged by the concrete
final-tuple theorem, never added to the frozen source target. -/
theorem allRows (data : Data) (window : Program 1) (oldStep : Program 4)
    (hguard : OriginalQuotientSpine.QuotientHasSpineGuard data window oldStep)
    (code : OTerm alpha) :
    Nonempty (Derivation body Gamma (spineRow (edgeChecker data oldStep) window code)) := by
  let edge := edgeChecker data oldStep
  let theta : Formula (alpha ⊕ Fin 1) := spineRow edge window (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [spineAtCode]
    exact zeroRow edge window
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body alpha 3 Gamma
    simp only [constructorBody,theta,spineAtIndex]
    let c : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph c h t
    let R := spineRow edge window t
    obtain ⟨d⟩ := consRow (body := body)
      (Gamma := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)) data window oldStep hguard c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  have h := actualOriginalListInductionAtCode body alpha Gamma theta code (andIntro hz hs)
  rw [spineAtCode] at h
  exact h

theorem positiveSpine (data : Data) (window : Program 1) (oldStep : Program 4)
    (hguard : OriginalQuotientSpine.QuotientHasSpineGuard data window oldStep)
    (x y code parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hp : Nonempty (Derivation body Gamma (positiveGraph (edgeChecker data oldStep) x y code parameter))) :
    Nonempty (Derivation body Gamma (OriginalSpineGuardLeaf.spineAccepted x y code parameter)) :=
  rowApply (edgeChecker data oldStep) window code x y parameter (allRows data window oldStep hguard code) hw hp

theorem positiveGuards (data : Data) (window : Program 1) (oldStep : Program 4)
    (hguard : OriginalQuotientSpine.QuotientHasSpineGuard data window oldStep)
    (hbottom : OriginalSpineNonBottom.SpineGuardRejectsBottom) :
    OriginalSameCodeSuffix.PositivePathGuards data window oldStep := by
  intro body alpha Gamma x y code typ parameter
  let P := OriginalSameCodeSuffix.positivePremises data window oldStep x y code typ parameter
  have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpath := andRight (andRight (andRight hp))
  have hs := positiveSpine data window oldStep hguard x y code parameter (andLeft hp) hpath
  obtain ⟨hb⟩ := hbottom body alpha (P :: Gamma) x y code parameter
  obtain ⟨hs'⟩ := hs
  have hn : Nonempty (Derivation body (P :: Gamma)
      (BottomRepresentative.bottomGraph InternalOriginalStepGuard.one x).not) :=
    ⟨Derivation.implicationElimination hb hs'⟩
  let xs : Fin 4 → OTerm alpha := Fin.cons x (Fin.cons y (Fin.cons code (Fin.cons parameter Fin.elim0)))
  have hnb := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs hn
  have hc := conjunctionAccept (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
    (InternalAcceptance.conjunction (PositiveGuard.spineGuard BottomSpineMeasure.measure)
      (InternalParameterizedPathChecker.checker (edgeChecker data oldStep) true)) xs hnb
    (conjunctionAccept (PositiveGuard.spineGuard BottomSpineMeasure.measure)
      (InternalParameterizedPathChecker.checker (edgeChecker data oldStep) true) xs ⟨hs'⟩ hpath)
  obtain ⟨hc⟩ := hc
  exact ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionProof
