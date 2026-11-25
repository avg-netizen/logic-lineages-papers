module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserversProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderOnEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomGuardOnProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileOnProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChildGuardEdgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field run)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEdgeObserverFitProof
open NumberedWindowInternalLiteralEdgeObserversProof
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalLiteralLeastOnObserverProof (exact_OpenLiteralSelectedObserverOn)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralHeaderOnEdgeProof (exact_OpenHeaderLeastIntro)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (exact_LiteralScalarEdgeCellHead)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomOnEdgeProof
open NumberedWindowInternalLiteralAtomGuardOnProof (exact_OpenAtomGuardOnEdge)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast functionHead)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralAuxProfileOnProof
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def childGuardObservers : List (Program 3) :=
  [unaryObserver cellHead, atomObserver, unaryObserver termShape,
    unaryObserver (maskedCoordinate (field 0)), unaryObserver (maskedCoordinate (field 1)),
    unaryObserver (maskedCoordinate functionHead)]

theorem exact_ChildGuardObserversStable (s : Settings) :
    ∀ O ∈ childGuardObservers, EdgeValueStable s O := by
  intro O h
  simp only [childGuardObservers,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · intro ctx ty a b g _ yes
    change run cellHead a = run cellHead b
    exact exact_LiteralScalarEdgeCellHead s g ty a b yes
  · exact exact_AtomicObserverStable s
  · exact exact_AuxShapeStable s
  · exact exact_AuxMaskedCoordinateStable s _ (Or.inl rfl)
  · exact exact_AuxMaskedCoordinateStable s _ (Or.inr (Or.inl rfl))
  · exact exact_AuxMaskedCoordinateStable s _ (Or.inr (Or.inr rfl))

private theorem headerOn (C : Program 3) (E : Program 4) (s : Settings)
    (stable : Preserves E (unaryObserver cellHead)) (L : Program 3) (ctx ty q k : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k))
    (held : D B Γ (programGraph L (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (headerLeast L) (suc k) ![ctx,ty,q]) := by
  apply programCases cellHead ![q] _
  intro β j Δ h keep head
  simp only [programRename,tripleInputsRename,sucRelabel]
  rw [unaryInputsRename] at head
  have old := renameInto actual j Δ keep
  rw [leastOnRename] at old
  have raw := renameInto held j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at raw
  let c := ctx.relabel j
  let t := ty.relabel j
  let a := q.relabel j
  let b := k.relabel j
  have moved := exact_OpenLiteralSelectedObserverOn C E s (unaryObserver cellHead) stable c t a b h old
    (exact_OpenUnaryObserverIntro cellHead c t a h head)
  exact exact_OpenHeaderLeastIntro L c t a b h raw head
    (exact_OpenUnaryObserverElim cellHead c t b h moved)

private theorem atomOn (C : Program 3) (E : Program 4) (s : Settings)
    (stable : Preserves E atomObserver) (L : Program 3) (ctx ty q k : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k))
    (held : D B Γ (programGraph L (suc k) ![ctx,ty,q])) :
    D B Γ (programGraph (guardedLeast L) (suc k) ![ctx,ty,q]) := by
  apply programCases atomicStamp ![q] _
  intro β j Δ stamp keep src
  simp only [programRename,tripleInputsRename,sucRelabel]
  rw [unaryInputsRename] at src
  have old := renameInto actual j Δ keep
  rw [leastOnRename] at old
  have raw := renameInto held j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at raw
  exact exact_OpenAtomGuardOnEdge C E s L stable (ctx.relabel j) (ty.relabel j) (q.relabel j) (k.relabel j)
    stamp old raw src

/-- Reassemble all three original child guard layers around an
arbitrary actually successful selected minimum. Every required
comparison was paid by the same physical round edge. -/
theorem exact_OpenChildGuardLeast (C : Program 3) (E : Program 4) (s : Settings)
    (installed : ∀ O ∈ childGuardObservers, Preserves E O) (ctx ty q k : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty q k)) :
    D B Γ (programGraph (childGuardedLeast (packedLeastOn C E s)) (suc k) ![ctx,ty,q]) := by
  let core := packedLeastOn C E s
  have shape := installed (unaryObserver termShape) (by simp [childGuardObservers])
  have first := installed (unaryObserver (maskedCoordinate (field 0))) (by simp [childGuardObservers])
  have second := installed (unaryObserver (maskedCoordinate (field 1))) (by simp [childGuardObservers])
  have head := installed (unaryObserver (maskedCoordinate functionHead)) (by simp [childGuardObservers])
  have tests := exact_OpenAuxProfileTestOn C E s shape first second head ctx ty q k actual
  have withProfile := exact_OpenAuxProfileFromTest core ctx ty q k actual tests
  have withHeader := headerOn C E s (installed (unaryObserver cellHead) (by simp [childGuardObservers]))
    (auxProfileLeast core) ctx ty q k actual withProfile
  exact atomOn C E s (installed atomObserver (by simp [childGuardObservers]))
    (headerLeast (auxProfileLeast core)) ctx ty q k actual withHeader

theorem exact_OpenChildGuardLeastInstalled (C : Program 3) (E : Program 4) (s : Settings) (ctx ty q k : OTerm α)
    (actual : D B Γ (leastOnGraph C (withObservers E childGuardObservers) s ctx ty q k)) :
    D B Γ (programGraph (childGuardedLeast (packedLeastOn C (withObservers E childGuardObservers) s))
      (suc k) ![ctx,ty,q]) :=
  exact_OpenChildGuardLeast C (withObservers E childGuardObservers) s
    (exact_OpenInstalledObserver E childGuardObservers) ctx ty q k actual

#print axioms exact_ChildGuardObserversStable
#print axioms exact_OpenChildGuardLeast
#print axioms exact_OpenChildGuardLeastInstalled
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChildGuardEdgeProof
