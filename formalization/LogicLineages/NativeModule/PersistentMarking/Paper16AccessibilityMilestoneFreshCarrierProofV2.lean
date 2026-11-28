module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierTargetsV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneDomainClosureProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontSyntaxOpenProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneVariableFrontWindowOpenProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadProofV2
import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneNamedLeafMemoProofV2
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverInstallNonAuxWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneFreshCarrierTargetsV2.FreshCarrierOnFrontWindow`
(K1 from the installed code at the front-tested leaves; Fable B2, 27 November 2026).

The fresh report is opened as in `exact_FreshApplicationFromLeast` into the parsed coordinates
`ctx`, `r = rawCons dom cod`, `fn` of the arrow address and the name of the fresh address, whose
payload is the named leaf `namedTerm 0 dom name`. Then, in order:

1. from the scalar of `q`: the context guard, the address scalar, literal membership of the
   arrow code, hence of `dom` (`exact_OpenLiteralFiniteDomain`), hence both type guards at `dom`
   and its membership in the grammar types; and the coverage report of `fn`, whose context half
   is the parsed context;
2. the window leaf (`exact_OpenVariableFrontWindow`) through the strict memo
   (`exact_OpenCoverInstallNonAuxWindow`), the syntax leaf (`exact_OpenVariableFrontSyntax`)
   through the syntax memo (`exact_NamedLeafUnitSyntax`), the own-cover occurrence
   (`exact_NamedLeafOwnCover`), hence the coverage report and both halves of the joined window
   (`exact_OpenSealedWindow`, `exact_NonAuxCoveredWindow`);
3. a least from coverage (`exact_OpenLeastOnFromCoverage`, `MemoSelectedReports`), which is the
   leaf itself (`exact_FreeSeedSelfLeast`);
4. the address scalar (`exact_OpenLiteralScalarFromSelfLeast`), the finite filter
   (`exact_MakeLiteralFiniteScalar`), transport to the selected fresh address.

The stored-type premise of `FreshAddressCarrier` is not used: the finite filter supplies the
literal membership of the stored arrow code. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalControlGraphSupportProof
  (compositionValue projectionValue programRename outputTransport headTransport valueUnique equalEqn)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (z suc eqn emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst)
open ID1Completion.InternalTagArithmeticSupportProof (symm congSuc sucNeZeroApply)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm packedFreeTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectChecks (exact_OpenParsedFresh)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
  (addressTerm addressReports arrowReports sourceShape parsedFreshAt)
open NumberedWindowInternalFreshProbeParsedTyped (chosenA)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalOriginalFirstHopCoreProof (exact_OriginalLiteralAddressReport)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedPrior namedMeasureBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicShapeProof (exact_OpenCoverNamedLeafIntrinsicShape)
open NumberedWindowInternalCoverInstallNonAuxWindowProof (exact_OpenCoverInstallNonAuxWindow)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralCanonicalChildProof (exact_OpenLiteralScalarFromSelfLeast)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralFiniteScalarGuardProof
  (finiteCodes finiteScalar exact_OpenLiteralFiniteScalar exact_MakeLiteralFiniteScalar)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (joinedAuxiliaryWindow exact_OpenJoinedAuxiliaryWindow)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralLeastOnMembersProof (hasLeastOn)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
  (selectedBiAuxType exact_OpenBiAuxTypeEvidence)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (leastSelectedAt FreshAddressCarrier)
open Paper16AccessibilityMilestoneDomainClosureTargetsV2 (DomainClosed)
open Paper16AccessibilityMilestoneDomainClosureProofV2 (exact_OpenLiteralFiniteDomain)
open Paper16AccessibilityMilestoneVariableFrontSyntaxTargetsV2 (variableFrontSyntax)
open Paper16AccessibilityMilestoneVariableFrontSyntaxOpenProofV2 (exact_OpenVariableFrontSyntax)
open Paper16AccessibilityMilestoneVariableFrontWindowTargetsV2 (variableFrontWindow)
open Paper16AccessibilityMilestoneVariableFrontWindowOpenProofV2 (exact_OpenVariableFrontWindow)
open Paper16AccessibilityMilestoneFreshPayloadProofV2 (exact_FreeSeedSelfLeast)
open Paper16AccessibilityMilestoneNamedLeafMemoProofV2
  (exact_NamedLeafUnitSyntax exact_NamedLeafOwnCover exact_NonAuxCoveredWindow)
open Paper16AccessibilityMilestoneFreshCarrierTargetsV2

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-! Syntax of the selected-least formula (as in `…FreshSeedLeastProofV2`, where these are
private). -/

private theorem tripleSubst {β : Type} (a b c : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![a, b, c] : Fin 3 → OTerm α) i).subst ts) =
      ![a.subst ts, b.subst ts, c.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

private theorem selectedIntro (L : Program 3) (ctx ty seed out : OTerm α)
    (d : Nonempty (Derivation body Γ (programGraph L (suc out) ![ctx, ty, seed]))) :
    Nonempty (Derivation body Γ (leastSelectedAt L ctx ty seed)) := by
  let f : Formula (α ⊕ Fin 1) := programGraph L (suc (.var (.inr 0)))
    ![ctx.relabel (Sum.inl : α → α ⊕ Fin 1), ty.relabel Sum.inl, seed.relabel Sum.inl]
  have h : instantiate f (emb out) = programGraph L (suc out) ![ctx, ty, seed] := by
    simp only [f, instantiate, bindEmbedding, programSubst, tripleSubst, sucSubst, liftBind, varBind]
  obtain ⟨d⟩ := d
  change Nonempty (Derivation body Γ (existsOne f))
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rwa [h]

private theorem selectedRename {β : Type} (L : Program 3) (ctx ty seed : OTerm α) (j : α → β) :
    (leastSelectedAt L ctx ty seed).relabel j =
      leastSelectedAt L (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [leastSelectedAt, existsRename, programRename, tripleInputsRename, sucRelabel,
    Term.relabel_relabel]
  rfl

private theorem selectedFromReports (C : Program 3) (s : Settings) (Base : Program 4)
    (selected : MemoSelectedReports C s Base) (ctx ty seed : OTerm α)
    (open_ : Nonempty (Derivation body Γ (hasLeastOn C (recursiveTypedMemo Base) s ctx ty seed))) :
    Nonempty (Derivation body Γ (leastSelectedAt (memoFilteredLeast C Base s) ctx ty seed)) := by
  obtain ⟨found⟩ := open_
  let m : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ψ : Formula (α ⊕ Fin 1) := leastOnGraph C (recursiveTypedMemo Base) s
    (ctx.relabel m) (ty.relabel m) (seed.relabel m) k
  let Ω : List (Formula (α ⊕ Fin 1)) := ψ :: Γ.map weaken
  have found' : Derivation body Γ (existsOne ψ) := found
  have row : Nonempty (Derivation body Ω ψ) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have report : Nonempty (Derivation body Ω (programGraph (memoFilteredLeast C Base s) (suc k)
      ![ctx.relabel m, ty.relabel m, seed.relabel m])) :=
    selected body (α ⊕ Fin 1) Ω (ctx.relabel m) (ty.relabel m) (seed.relabel m) k row
  have last : Nonempty (Derivation body Ω
      (weaken (leastSelectedAt (memoFilteredLeast C Base s) ctx ty seed))) := by
    change Nonempty (Derivation body Ω
      ((leastSelectedAt (memoFilteredLeast C Base s) ctx ty seed).relabel m))
    rw [selectedRename]
    exact selectedIntro (memoFilteredLeast C Base s) (ctx.relabel m) (ty.relabel m)
      (seed.relabel m) k report
  obtain ⟨last⟩ := last
  exact ⟨Derivation.existentialElimination found' last⟩

/-! Address reports. -/

private theorem namedRename {β : Type} (tag : Nat) (ty i : OTerm α) (j : α → β) :
    (namedTerm tag ty i).relabel j = namedTerm tag (ty.relabel j) (i.relabel j) := by
  simp only [namedTerm, rawConsRename, numeralRename, zRelabel]

private theorem reportTransport (s t c ty k : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn s t)))
    (report : Nonempty (Derivation body Γ (addressReport s c ty k))) :
    Nonempty (Derivation body Γ (addressReport t c ty k)) := by
  obtain ⟨r⟩ := report
  have r' : Derivation body Γ (programGraph addressGood (suc z) ![s] ⊓
      (programGraph rawContext c ![s] ⊓ (programGraph rawResult ty ![s] ⊓
        programGraph rawLeast k ![s]))) := r
  obtain ⟨g⟩ := headTransport addressGood (suc z) s t ![] same ⟨Derivation.conjunctionLeft r'⟩
  obtain ⟨x⟩ := headTransport rawContext c s t ![] same
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r')⟩
  obtain ⟨y⟩ := headTransport rawResult ty s t ![] same
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r'))⟩
  obtain ⟨l⟩ := headTransport rawLeast k s t ![] same
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight r'))⟩
  have out : Derivation body Γ (programGraph addressGood (suc z) ![t] ⊓
      (programGraph rawContext c ![t] ⊓ (programGraph rawResult ty ![t] ⊓
        programGraph rawLeast k ![t]))) :=
    Derivation.conjunctionIntroduction g
      (Derivation.conjunctionIntroduction x (Derivation.conjunctionIntroduction y l))
  exact ⟨out⟩

private theorem resultField (q ctx ty k : OTerm α)
    (shell : Nonempty (Derivation body Γ (addressReport q ctx ty k))) :
    Nonempty (Derivation body Γ (unary rawResult ty q)) := by
  obtain ⟨r⟩ := shell
  have r' : Derivation body Γ (unary addressGood (suc z) q ⊓
      (unary rawContext ctx q ⊓ (unary rawResult ty q ⊓ unary rawLeast k q))) := r
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r'))⟩

/-- The three checks of an accepted address scalar at a reported address (`fieldsValid` of
`NumberedWindowInternalLiteralApplicationInputCoordinatesProof`, private there). -/
private theorem fieldsValid (cv tv : Program 1) (W L : Program 3) (q ctx ty k : OTerm α)
    (shell : Nonempty (Derivation body Γ (addressReport q ctx ty k)))
    (scalar : Nonempty (Derivation body Γ (unary (addressScalar cv tv W L) (suc z) q))) :
    Nonempty (Derivation body Γ (unary cv (suc z) ctx)) ∧
      Nonempty (Derivation body Γ (unary tv (suc z) ty)) ∧
      Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  obtain ⟨f⟩ := reported cv tv W L body α Γ q ctx ty k
  obtain ⟨atQ⟩ := shell
  obtain ⟨ok⟩ := scalar
  let got := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination f atQ)) ok
  obtain ⟨g⟩ := openTest W L body α Γ ctx ty k
  let valid := Derivation.implicationElimination (Derivation.conjunctionLeft g)
    (Derivation.conjunctionRight (Derivation.conjunctionRight got))
  exact ⟨⟨Derivation.conjunctionLeft got⟩,
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight got)⟩,
    ⟨Derivation.conjunctionLeft valid⟩⟩

/-! The parsed context. -/

/-- The window leaf report at a free-variable leaf, from the context half of any coverage
report at the same context. -/
private theorem leafWindowFromPresent (T : Program 1) (base : Program 2) (ctx q ty i : OTerm α)
    (present : Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx, z, q])))
    (typed : Nonempty (Derivation body Γ (unary T (suc z) ty))) :
    Nonempty (Derivation body Γ
      (programGraph (variableFrontWindow T base) (suc ty) ![ctx, namedTerm 0 ty i])) := by
  apply optionGraphCases contextOption (![ctx, z, q] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename, zRelabel] at zero
    have yes := renameInto present j Δ keep
    simp only [programRename, tripleInputsRename, sucRelabel, zRelabel] at yes
    let xs : Fin 3 → OTerm β := ![ctx.relabel j, z, q.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs
      zero yes
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename, zRelabel] at parsed
    simp only [programRename, binaryInputsRename, sucRelabel, namedRename]
    have typed' := renameInto typed j Δ keep
    simp only [unaryRename, sucRelabel, zRelabel] at typed'
    have read : Nonempty (Derivation body Δ (unary parser (suc payload) (ctx.relabel j))) := by
      apply compositionRecover parser (fun _ : Fin 1 => (.projection 0 : Program 3)) (suc payload)
        ![ctx.relabel j, z, q.relabel j] ![ctx.relabel j] parsed
      intro k
      obtain rfl := Fin.eq_zero k
      exact projectionValue (0 : Fin 3) ![ctx.relabel j, z, q.relabel j]
    exact exact_OpenVariableFrontWindow T base body β Δ (ctx.relabel j) (ty.relabel j)
      (i.relabel j) payload read typed'

/-- The context half of a coverage report does not depend on the seed. -/
private theorem presentAt (ctx q q' : OTerm α)
    (present : Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx, z, q]))) :
    Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx, z, q'])) := by
  apply optionGraphCases contextOption (![ctx, z, q] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename, zRelabel] at zero
    have yes := renameInto present j Δ keep
    simp only [programRename, tripleInputsRename, sucRelabel, zRelabel] at yes
    let xs : Fin 3 → OTerm β := ![ctx.relabel j, z, q.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs
      zero yes
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename, zRelabel] at parsed
    simp only [programRename, tripleInputsRename, sucRelabel, zRelabel]
    let xs : Fin 3 → OTerm β := ![ctx.relabel j, z, q'.relabel j]
    have read : Nonempty (Derivation body Δ (unary parser (suc payload) (ctx.relabel j))) := by
      apply compositionRecover parser (fun _ : Fin 1 => (.projection 0 : Program 3)) (suc payload)
        ![ctx.relabel j, z, q.relabel j] ![ctx.relabel j] parsed
      intro k
      obtain rfl := Fin.eq_zero k
      exact projectionValue (0 : Fin 3) ![ctx.relabel j, z, q.relabel j]
    have again : Nonempty (Derivation body Δ (programGraph contextOption (suc payload) xs)) := by
      apply compositionValue parser (fun _ : Fin 1 => (.projection 0 : Program 3)) (suc payload) xs
        ![ctx.relabel j] read
      intro k
      obtain rfl := Fin.eq_zero k
      exact projectionValue (0 : Fin 3) xs
    exact successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload xs
      again (oneConstantValue xs)

/-! Coverage and least at the leaf. -/

private theorem ownSeedAtLeaf (V TV M : Program 1) (s : Settings) (ctx ty i : OTerm α)
    (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (valid : Nonempty (Derivation body Γ (unary (unitAuxSyntax V TV) (suc z) (namedTerm 0 ty i)))) :
    Nonempty (Derivation body Γ (programGraph
      (ownSeed (measuredStrictCover V TV (namedMeasureBase M)) s) (suc z)
      ![ctx, z, namedTerm 0 ty i])) := by
  let C := measuredStrictCover V TV (namedMeasureBase M)
  apply programCases (scratchVertices C s) ![namedTerm 0 ty i] _
  intro β j Δ vertices keep pool
  simp only [unaryInputsRename, namedRename] at pool
  simp only [programRename, tripleInputsRename, sucRelabel, zRelabel, namedRename]
  have member' := renameInto member j Δ keep
  simp only [graphRename, typesTerm, numeralRename] at member'
  have valid' := renameInto valid j Δ keep
  simp only [unaryRename, sucRelabel, zRelabel, namedRename] at valid'
  let leaf : OTerm β := namedTerm 0 (ty.relabel j) (i.relabel j)
  let xs : Fin 3 → OTerm β := ![ctx.relabel j, z, leaf]
  have pool' : Nonempty (Derivation body Δ (unary (scratchVertices C s) vertices leaf)) := pool
  have hit := exact_NamedLeafOwnCover V TV M s body β Δ (ty.relabel j) (i.relabel j) vertices
    member' valid' pool'
  apply compositionValue scratchMember ![poolAtSeed C s, .projection 2] (suc z) xs
    ![vertices, leaf] hit
  intro k
  refine Fin.cases ?_ (fun l => ?_) k
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => (.projection 2 : Program 3))
      vertices xs ![leaf] pool'
    intro l
    obtain rfl := Fin.eq_zero l
    exact projectionValue (2 : Fin 3) xs
  · obtain rfl := Fin.eq_zero l
    exact projectionValue (2 : Fin 3) xs

/-- A selected report of a guarded least at a free-variable leaf is a self-least report. -/
private theorem selfLeastOfSelected (L' : Program 3) (ctx ty a n : OTerm α)
    (sel : Nonempty (Derivation body Γ
      (leastSelectedAt (guardedLeast L') ctx ty (namedTerm 0 a n)))) :
    Nonempty (Derivation body Γ (programGraph (guardedLeast L') (suc (namedTerm 0 a n))
      ![ctx, ty, namedTerm 0 a n])) := by
  obtain ⟨found⟩ := sel
  let m : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let ψ : Formula (α ⊕ Fin 1) := programGraph (guardedLeast L') (suc k)
    ![ctx.relabel m, ty.relabel m, (namedTerm 0 a n).relabel m]
  let Ω : List (Formula (α ⊕ Fin 1)) := ψ :: Γ.map weaken
  have found' : Derivation body Γ (existsOne ψ) := found
  have row : Nonempty (Derivation body Ω (programGraph (guardedLeast L') (suc k)
      ![ctx.relabel m, ty.relabel m, (namedTerm 0 a n).relabel m])) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  rw [namedRename] at row
  obtain ⟨same⟩ := exact_FreeSeedSelfLeast L' body (α ⊕ Fin 1) Ω (ctx.relabel m) (ty.relabel m)
    (a.relabel m) (n.relabel m) k row
  have atSeed := outputTransport (guardedLeast L') (suc k)
    (suc (namedTerm 0 (a.relabel m) (n.relabel m)))
    ![ctx.relabel m, ty.relabel m, namedTerm 0 (a.relabel m) (n.relabel m)]
    ⟨congSuc (symm same)⟩ row
  have last : Nonempty (Derivation body Ω (weaken (programGraph (guardedLeast L')
      (suc (namedTerm 0 a n)) ![ctx, ty, namedTerm 0 a n]))) := by
    change Nonempty (Derivation body Ω ((programGraph (guardedLeast L')
      (suc (namedTerm 0 a n)) ![ctx, ty, namedTerm 0 a n]).relabel m))
    simp only [programRename, tripleInputsRename, sucRelabel, namedRename]
    exact atSeed
  obtain ⟨last⟩ := last
  exact ⟨Derivation.existentialElimination found' last⟩

/-! K1. -/

theorem exact_FreshCarrierOnFrontWindow : FreshCarrierOnFrontWindow := by
  intro S K W A s X base₀ T V₀ baseM₀ Tg V baseM base C Base scalarEq leastEq selected guards
    domClosed c σ τ _listed α Γ q u held _stored fresh
  let body := sourceBody A.presentation c
  let cv := A.contextGuard
  let tv := A.typeGuard
  let Q := joinedAuxiliaryWindow s base Tg V tv baseM
  let i₀ := addressScalar cv tv Q A.least
  have parsed := exact_OpenParsedFresh A.probes.scalarProg A.probes.freshBound body α Γ q u fresh
  unfold parsedFreshAt at parsed
  apply actualFiniteExistentialElimination body α 6 Γ _ (carrier A.presentation false c u) parsed
  rw [carrierRename]
  let j : α → α ⊕ Fin 6 := Sum.inl
  let q₁ : OTerm (α ⊕ Fin 6) := q.relabel j
  let u₁ : OTerm (α ⊕ Fin 6) := u.relabel j
  let ctx : OTerm (α ⊕ Fin 6) := .var (.inr 0)
  let r : OTerm (α ⊕ Fin 6) := .var (.inr 1)
  let dom : OTerm (α ⊕ Fin 6) := .var (.inr 2)
  let cod : OTerm (α ⊕ Fin 6) := .var (.inr 3)
  let fn : OTerm (α ⊕ Fin 6) := .var (.inr 4)
  let name : OTerm (α ⊕ Fin 6) := .var (.inr 5)
  let leaf : OTerm (α ⊕ Fin 6) := namedTerm 0 dom name
  let prior : OTerm (α ⊕ Fin 6) := namedPrior false dom name
  let R : Formula (α ⊕ Fin 6) := addressReports q₁ ctx r fn ⊓ (arrowReports q₁ dom cod ⊓
    (sourceShape q₁ ctx r dom cod fn ⊓
      (programGraph A.probes.freshBound name ![fn] ⊓ equal u₁ (packedFreeTerm ctx dom name))))
  let Δ : List (Formula (α ⊕ Fin 6)) := R :: Γ.map (fun f => f.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := fun f hf =>
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
  have main : Nonempty (Derivation body Δ (carrier A.presentation false c u₁)) := by
    have head : Derivation body Δ R := Derivation.hypothesis List.mem_cons_self
    have rest₁ := Derivation.conjunctionRight head
    have rest₂ := Derivation.conjunctionRight rest₁
    have shape : Derivation body Δ (equal q₁ (addressTerm ctx r fn) ⊓ equal r (consTerm dom cod)) :=
      Derivation.conjunctionLeft rest₂
    have uShape : Derivation body Δ (equal u₁ (packedFreeTerm ctx dom name)) :=
      Derivation.conjunctionRight (Derivation.conjunctionRight rest₂)
    have qEq : Derivation body Δ (eqn q₁ (addressTerm ctx r fn)) := by
      have h := Derivation.conjunctionLeft shape
      rw [equalEqn] at h
      exact h
    have rEq : Derivation body Δ (eqn r (rawCons dom cod)) := by
      have h := Derivation.conjunctionRight shape
      rw [equalEqn] at h
      exact h
    have uEq : Derivation body Δ (eqn u₁ (addressTerm ctx dom leaf)) := by
      have h := uShape
      rw [equalEqn] at h
      exact h
    have held₁ := renameInto held j Δ keep
    rw [carrierRename] at held₁
    -- 1. the scalar of the arrow address
    have fScalar : Nonempty (Derivation body Δ (programGraph A.scalar (suc z) ![q₁])) :=
      (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
        false c body (α ⊕ Fin 6) Δ q₁).mp held₁
    have fFinite : Nonempty (Derivation body Δ
        (unary (finiteScalar i₀ (finiteCodes W)) (suc z) q₁)) := by
      have h := fScalar
      rw [scalarEq] at h
      exact h
    have qLiteral : Nonempty (Derivation body Δ (addressReport (addressTerm ctx r fn) ctx r fn)) :=
      exact_OriginalLiteralAddressReport ctx r fn
    obtain ⟨qReport⟩ := reportTransport (addressTerm ctx r fn) q₁ ctx r fn ⟨symm qEq⟩ qLiteral
    have qReport' : Derivation body Δ (programGraph addressGood (suc z) ![q₁] ⊓
        (programGraph rawContext ctx ![q₁] ⊓ (programGraph rawResult r ![q₁] ⊓
          programGraph rawLeast fn ![q₁]))) := qReport
    obtain ⟨arrowField⟩ := outputTransport rawResult r (rawCons dom cod) ![q₁] ⟨rEq⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight qReport'))⟩
    have fAddress : Nonempty (Derivation body Δ (addressReport q₁ ctx (rawCons dom cod) fn)) := by
      have out : Derivation body Δ (programGraph addressGood (suc z) ![q₁] ⊓
          (programGraph rawContext ctx ![q₁] ⊓ (programGraph rawResult (rawCons dom cod) ![q₁] ⊓
            programGraph rawLeast fn ![q₁]))) :=
        Derivation.conjunctionIntroduction (Derivation.conjunctionLeft qReport')
          (Derivation.conjunctionIntroduction
            (Derivation.conjunctionLeft (Derivation.conjunctionRight qReport'))
            (Derivation.conjunctionIntroduction arrowField
              (Derivation.conjunctionRight (Derivation.conjunctionRight
                (Derivation.conjunctionRight qReport')))))
      exact ⟨out⟩
    obtain ⟨fAddressScalar, arrowIn⟩ := exact_OpenLiteralFiniteScalar i₀ (finiteCodes W) q₁
      (rawCons dom cod) (resultField q₁ ctx (rawCons dom cod) fn fAddress) fFinite
    have domIn : Nonempty (Derivation body Δ (literalMembership (finiteCodes W) dom)) :=
      exact_OpenLiteralFiniteDomain W domClosed body (α ⊕ Fin 6) Δ dom cod arrowIn
    obtain ⟨domTg, domTv⟩ := guards body (α ⊕ Fin 6) Δ dom domIn
    have memberTypes : Nonempty (Derivation body Δ (memberGraph (typesTerm s (α ⊕ Fin 6)) dom)) :=
      (exact_OpenBiAuxTypeEvidence s T tv dom dom domTg domTg).domain
    obtain ⟨gc, _, fWindow⟩ := fieldsValid cv tv Q A.least q₁ ctx (rawCons dom cod) fn fAddress
      fAddressScalar
    have fSealed :=
      ((exact_OpenJoinedAuxiliaryWindow s base Tg V tv baseM ctx (rawCons dom cod) fn).mp fWindow).1
    have fnCover : Nonempty (Derivation body Δ (coverageReport C s ctx fn)) :=
      ((exact_OpenSealedWindow C s (strictAuxWindow base Tg) ctx (rawCons dom cod) fn).1 fSealed).2
    obtain ⟨both⟩ := conjunctionRecover contextPresent (ownSeed C s) ![ctx, z, fn] fnCover
    have present : Nonempty (Derivation body Δ (programGraph contextPresent (suc z) ![ctx, z, fn])) :=
      ⟨Derivation.conjunctionLeft both⟩
    -- 2. the joined window of the leaf
    have leafShape : Nonempty (Derivation body Δ (unary termShape z leaf)) :=
      (exact_OpenCoverNamedLeafIntrinsicShape false body (α ⊕ Fin 6) Δ dom name).1
    have leafReport : Nonempty (Derivation body Δ (programGraph base (suc dom) ![ctx, leaf])) :=
      leafWindowFromPresent Tg base₀ ctx fn dom name present domTg
    have strictLeaf : Nonempty (Derivation body Δ
        (windowGraph (strictAuxWindow base Tg) ctx dom leaf)) :=
      exact_OpenCoverInstallNonAuxWindow base Tg body (α ⊕ Fin 6) Δ ctx prior dom leafShape
        leafReport
    have vLeaf : Nonempty (Derivation body Δ (unary V (suc z) leaf)) :=
      exact_OpenVariableFrontSyntax tv V₀ body (α ⊕ Fin 6) Δ dom name (suc z) domTv
    have vaLeaf : Nonempty (Derivation body Δ (unary (unitAuxSyntax V tv) (suc z) leaf)) :=
      exact_NamedLeafUnitSyntax V tv body (α ⊕ Fin 6) Δ dom name vLeaf
    have ownLeaf : Nonempty (Derivation body Δ
        (programGraph (ownSeed C s) (suc z) ![ctx, z, leaf])) :=
      ownSeedAtLeaf V tv baseM₀ s ctx dom name memberTypes vaLeaf
    have leafCover : Nonempty (Derivation body Δ (coverageReport C s ctx leaf)) :=
      conjunctionAccept contextPresent (ownSeed C s) ![ctx, z, leaf]
        (presentAt ctx fn leaf present) ownLeaf
    have sealedLeaf :=
      (exact_OpenSealedWindow C s (strictAuxWindow base Tg) ctx dom leaf).2 strictLeaf leafCover
    have coveredLeaf := exact_NonAuxCoveredWindow C s base Tg (unitAuxSyntax V tv) body
      (α ⊕ Fin 6) Δ ctx prior dom leafShape leafReport vaLeaf leafCover
    have leafWindow : Nonempty (Derivation body Δ (windowAt Q ctx dom leaf)) :=
      (exact_OpenJoinedAuxiliaryWindow s base Tg V tv baseM ctx dom leaf).mpr
        ⟨sealedLeaf, coveredLeaf⟩
    -- 3. the self-least of the leaf
    have leastOn : Nonempty (Derivation body Δ
        (hasLeastOn C (recursiveTypedMemo Base) s ctx dom leaf)) :=
      exact_OpenLeastOnFromCoverage C (recursiveTypedMemo Base) s ctx dom leaf leafCover
    have chosen : Nonempty (Derivation body Δ
        (leastSelectedAt (memoFilteredLeast C Base s) ctx dom leaf)) :=
      selectedFromReports C s Base selected ctx dom leaf leastOn
    have selfMemo : Nonempty (Derivation body Δ (programGraph (memoFilteredLeast C Base s)
        (suc leaf) ![ctx, dom, leaf])) :=
      selfLeastOfSelected _ ctx dom dom name chosen
    have selfLeast : Nonempty (Derivation body Δ
        (programGraph A.least (suc leaf) ![ctx, dom, leaf])) := by
      rw [leastEq]
      exact selfMemo
    -- 4. the scalar of the fresh address
    have addressAccepted : Nonempty (Derivation body Δ
        (unary i₀ (suc z) (addressTerm ctx dom leaf))) :=
      exact_OpenLiteralScalarFromSelfLeast cv tv Q A.least ctx dom leaf gc domTv leafWindow selfLeast
    have uLiteral : Nonempty (Derivation body Δ
        (addressReport (addressTerm ctx dom leaf) ctx dom leaf)) :=
      exact_OriginalLiteralAddressReport ctx dom leaf
    have finiteAccepted : Nonempty (Derivation body Δ
        (unary (finiteScalar i₀ (finiteCodes W)) (suc z) (addressTerm ctx dom leaf))) :=
      exact_MakeLiteralFiniteScalar i₀ (finiteCodes W) (addressTerm ctx dom leaf) dom
        (resultField (addressTerm ctx dom leaf) ctx dom leaf uLiteral) addressAccepted domIn
    have atFresh : Nonempty (Derivation body Δ
        (programGraph (finiteScalar i₀ (finiteCodes W)) (suc z) ![u₁])) :=
      headTransport (finiteScalar i₀ (finiteCodes W)) (suc z) (addressTerm ctx dom leaf) u₁ ![]
        ⟨symm uEq⟩ finiteAccepted
    have uScalar : Nonempty (Derivation body Δ (programGraph A.scalar (suc z) ![u₁])) := by
      rw [scalarEq]
      exact atFresh
    exact (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body (α ⊕ Fin 6) Δ u₁).mpr uScalar
  exact main

#print axioms exact_FreshCarrierOnFrontWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshCarrierProofV2
