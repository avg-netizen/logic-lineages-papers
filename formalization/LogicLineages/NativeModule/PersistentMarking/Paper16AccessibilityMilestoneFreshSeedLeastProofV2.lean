module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteScalarGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteCodomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2.SeedLeastOnJoinedWindow`
(K2 from the installed code; Fable B2, 27 November 2026).

Every step is an accepted open-term law of the legacy tree; this module only composes them.

1. The two carriers are scalar acceptances (`exact_DomainRules`); the finite filter gives the
   address scalar and literal membership of both stored types (`exact_OpenLiteralFiniteScalar`),
   and child closure of the window gives it for the codomain (`exact_OpenLiteralFiniteCodomain`).
2. The open type guards turn the two memberships into the parent type evidence
   (`exact_OpenBiAuxTypeEvidence`).
3. The address scalar at a reported address yields the joined auxiliary window of its fields
   (`reported`, `openTest`).
4. `exact_OpenJoinedAuxiliaryParent` forms the joined window of the application seed from the
   two child windows: this is where the visible syntax wrapper accepts the auxiliary node
   (`exact_OpenUnitAuxSyntaxIntro`) and the explicit generator lists it
   (`exact_OpenSelectedGrammarAuxScratchMeasured`). Its sealed half reports the seed in its own
   cover (`exact_OpenSealedWindow`).
5. Coverage gives a least under `packedLeastOn` for any edge program
   (`exact_OpenLeastOnFromCoverage`, which rests on `exact_OpenLeastOnFromSeed`), and
   `MemoSelectedReports` lifts it to the installed guarded program.

The stored-type and fresh-selector premises of `FreshSeedLeast` are not used: the law holds for
any two scalar carriers with these address reports. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (z suc emb bindEmbedding liftBind varBind sucRelabel sucSubst)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (joinedBiAuxBase)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralFiniteCodomainProof (exact_OpenLiteralFiniteCodomain)
open NumberedWindowInternalLiteralFiniteScalarGuardProof
  (finiteCodes finiteScalar exact_OpenLiteralFiniteScalar)
open NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof
  (joinedAuxiliaryWindow exact_OpenJoinedAuxiliaryWindow exact_OpenJoinedAuxiliaryParent)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralLeastOnMembersProof (hasLeastOn)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralRankForwardRowsProof (OpenRankTypeGuards)
open NumberedWindowInternalLiteralSealedWindowProof (exact_OpenSealedWindow)
open NumberedWindowInternalLiteralStrictMeasuredMemoTransportProof
  (selectedBiAuxType exact_OpenBiAuxTypeEvidence)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneTargetsV2 (InstalledWindow)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (leastSelectedAt FreshSeedLeast)
open Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2

attribute [local irreducible] programGraph

private theorem tripleSubst {α β : Type} (a b c : OTerm α) (ts : α → OTerm β) :
    (fun i => ((![a, b, c] : Fin 3 → OTerm α) i).subst ts) =
      ![a.subst ts, b.subst ts, c.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y =>
    Fin.cases ?_ (fun noIndex => Fin.elim0 noIndex) y) x) i <;> rfl

/-- The successor report of a least program at a chosen value is a selected report. -/
private theorem selectedIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (L : Program 3) (ctx ty seed out : OTerm α)
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

private theorem selectedRename {α β : Type} (L : Program 3) (ctx ty seed : OTerm α) (j : α → β) :
    (leastSelectedAt L ctx ty seed).relabel j =
      leastSelectedAt L (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [leastSelectedAt, existsRename, programRename, tripleInputsRename, sucRelabel,
    Term.relabel_relabel] <;> rfl

/-- The least-report law carries an open-domain report of the unguarded packed least to a
selected report of the installed guarded program. -/
private theorem selectedFromReports {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (Base : Program 4) (selected : MemoSelectedReports C s Base)
    (ctx ty seed : OTerm α)
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

/-- An accepted address scalar at a reported address yields the installed window of its
fields (the window conjunct of `fieldsValid` in
`NumberedWindowInternalLiteralApplicationInputCoordinatesProof`, which is private there). -/
private theorem windowOfScalar {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (cv tv : Program 1) (W L : Program 3) (q ctx ty k : OTerm α)
    (shell : Nonempty (Derivation body Γ (addressReport q ctx ty k)))
    (scalar : Nonempty (Derivation body Γ (unary (addressScalar cv tv W L) (suc z) q))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  obtain ⟨f⟩ := reported cv tv W L body α Γ q ctx ty k
  obtain ⟨atQ⟩ := shell
  obtain ⟨ok⟩ := scalar
  let got := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination f atQ)) ok
  obtain ⟨g⟩ := openTest W L body α Γ ctx ty k
  let valid := Derivation.implicationElimination (Derivation.conjunctionLeft g)
    (Derivation.conjunctionRight (Derivation.conjunctionRight got))
  exact ⟨Derivation.conjunctionLeft valid⟩

/-- The stored result field of an address report. -/
private theorem resultField {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (q ctx ty k : OTerm α)
    (shell : Nonempty (Derivation body Γ (addressReport q ctx ty k))) :
    Nonempty (Derivation body Γ (unary rawResult ty q)) := by
  obtain ⟨r⟩ := shell
  have r' : Derivation body Γ (unary addressGood (suc z) q ⊓
      (unary rawContext ctx q ⊓ (unary rawResult ty q ⊓ unary rawLeast k q))) := r
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r'))⟩

theorem exact_SeedLeastOnJoinedWindow : SeedLeastOnJoinedWindow := by
  intro S K W A s X base T V baseM Tg C Base scalarEq leastEq selected guards c σ τ _listed
    α Γ q u ctx dom cod fn arg held uHeld _stored _fresh fAddress uAddress
  let body := sourceBody A.presentation c
  let cv := A.contextGuard
  let tv := A.typeGuard
  let Q := joinedAuxiliaryWindow s base Tg V tv baseM
  let i₀ := addressScalar cv tv Q A.least
  let p := auxiliaryTerm dom cod fn arg
  -- 1. scalar acceptances, finite memberships
  have fScalar : Nonempty (Derivation body Γ (programGraph A.scalar (suc z) ![q])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body α Γ q).mp held
  have uScalar : Nonempty (Derivation body Γ (programGraph A.scalar (suc z) ![u])) :=
    (exact_DomainRules A.scalar (jRaw A.scalar) A.path (dCore A.scalar A.path permutation)
      false c body α Γ u).mp uHeld
  have fFinite : Nonempty (Derivation body Γ (unary (finiteScalar i₀ (finiteCodes W)) (suc z) q)) := by
    have h := fScalar
    rw [scalarEq] at h
    exact h
  have uFinite : Nonempty (Derivation body Γ (unary (finiteScalar i₀ (finiteCodes W)) (suc z) u)) := by
    have h := uScalar
    rw [scalarEq] at h
    exact h
  obtain ⟨fAddressScalar, arrowIn⟩ := exact_OpenLiteralFiniteScalar i₀ (finiteCodes W) q
    (rawCons dom cod) (resultField q ctx (rawCons dom cod) fn fAddress) fFinite
  obtain ⟨uAddressScalar, domIn⟩ := exact_OpenLiteralFiniteScalar i₀ (finiteCodes W) u
    dom (resultField u ctx dom arg uAddress) uFinite
  have codIn : Nonempty (Derivation body Γ (literalMembership (finiteCodes W) cod)) :=
    exact_OpenLiteralFiniteCodomain W A.valid.2.1 dom cod arrowIn
  -- 2. parent type evidence
  obtain ⟨domGuard, _⟩ := guards body α Γ dom domIn
  obtain ⟨codGuard, _⟩ := guards body α Γ cod codIn
  have types := exact_OpenBiAuxTypeEvidence s T tv dom cod domGuard codGuard
  -- 3. child windows
  have fWindow : Nonempty (Derivation body Γ (windowAt Q ctx (rawCons dom cod) fn)) :=
    windowOfScalar cv tv Q A.least q ctx (rawCons dom cod) fn fAddress fAddressScalar
  have aWindow : Nonempty (Derivation body Γ (windowAt Q ctx dom arg)) :=
    windowOfScalar cv tv Q A.least u ctx dom arg uAddress uAddressScalar
  -- 4. the parent window and its coverage report
  obtain ⟨parent, _⟩ := exact_OpenJoinedAuxiliaryParent s base Tg V tv baseM ctx dom cod fn arg
    types fWindow aWindow
  have sealedHalf := ((exact_OpenJoinedAuxiliaryWindow s base Tg V tv baseM ctx cod p).mp parent).1
  have cover : Nonempty (Derivation body Γ (coverageReport C s ctx p)) :=
    ((exact_OpenSealedWindow C s (strictAuxWindow base Tg) ctx cod p).1 sealedHalf).2
  -- 5. least under the packed program, lifted to the installed program
  have leastOn : Nonempty (Derivation body Γ (hasLeastOn C (recursiveTypedMemo Base) s ctx cod p)) :=
    exact_OpenLeastOnFromCoverage C (recursiveTypedMemo Base) s ctx cod p cover
  have finalReport : Nonempty (Derivation body Γ
      (leastSelectedAt (memoFilteredLeast C Base s) ctx cod p)) :=
    selectedFromReports C s Base selected ctx cod p leastOn
  rw [leastEq]
  exact finalReport

#print axioms exact_SeedLeastOnJoinedWindow

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshSeedLeastProofV2
