module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedRawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalEqualityTest (equalityTest)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelope (nodeGood applyUnary exactBody)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm bottomTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (replaceRawSource)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicTypedRawProof
  (atomicTypedRaw exact_OpenLiteralAtomicTypedFreeTarget exact_OpenLiteralAtomicTypedBottomReject)
open NumberedWindowInternalLiteralAtomicRawIntroProof
  (exact_OpenLiteralGuardedRawNonAtom exact_OpenLiteralGuardedFreeRawIntro)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fiveRename {β : Type} (a b c d e : OTerm α) (j : α → β) :
    (fun i : Fin 5 => ((![a,b,c,d,e] : Fin 5 → OTerm α) i).relabel j) =
      ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun n => Fin.elim0 n))))) i

private theorem nodeZero (tag n : Nat) (q : OTerm α)
    (denied : D B Γ (unary (nodeGood (literal 1 tag) n) (suc z) q).not) :
    D B Γ (unary (nodeGood (literal 1 tag) n) z q) :=
  conjunctionReject cellGood
    (conjunction (.composition equalityTest ![cellHead,literal 1 tag]) (applyUnary (exactBody n) cellTail))
    ![q] denied

/-- The exact open consequences of the free and bottom constructors
are enough to rebuild the selected test for every real raw call. -/
structure RawAtoms (raw : Program 5) : Prop where
  free : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty t n w r : OTerm α),
    D B Γ (programGraph raw (suc z) ![ctx,ty,freeTerm t n,w,r]) → D B Γ (eqn r (bottomTerm t))
  bottom : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty t w r : OTerm α),
    D B Γ (programGraph raw (suc z) ![ctx,ty,bottomTerm t,w,r]) → D B Γ ⊥

theorem exact_OpenLiteralRawGuardReturnFromAtoms (raw : Program 5) (atoms : RawAtoms raw)
    (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (guardedRaw raw) (suc z) ![ctx,ty,q,w,r]) := by
  let result := programGraph (guardedRaw raw) (suc z) ![ctx,ty,q,w,r]
  let F := unary freeTest (suc z) q
  let T := unary bottomTest (suc z) q
  have atFree : D B (F :: Γ) result := by
    have trueF : D B (F :: Γ) F := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := held
    apply nodeAtCases 0 2 0 ![q,w,r] result (onTape freeTest 0 (suc z) ![q,w,r] trueF)
    intro β j Δ fields keep count shape _
    rcases fields with _ | ⟨t,_ | ⟨n,_ | ⟨d,ds⟩⟩⟩ <;> simp at count
    rw [programRename,fiveRename,sucRelabel,zRelabel]
    have raw' := renameInto (⟨addHyp h F⟩ : D B (F :: Γ) (programGraph raw (suc z) ![ctx,ty,q,w,r])) j Δ keep
    simp only [programRename,fiveRename,sucRelabel,zRelabel] at raw'
    have toAtom := replaceRawSource raw (ctx.relabel j) (ty.relabel j) (q.relabel j) (freeTerm t n)
      (w.relabel j) (r.relabel j) shape raw'
    have target := atoms.free B β Δ (ctx.relabel j) (ty.relabel j) t n
      (w.relabel j) (r.relabel j) toAtom
    have ret := exact_OpenLiteralGuardedFreeRawIntro raw (ctx.relabel j) (ty.relabel j) t n
      (w.relabel j) (r.relabel j) toAtom target
    obtain ⟨same⟩ := shape
    exact replaceRawSource (guardedRaw raw) (ctx.relabel j) (ty.relabel j) (freeTerm t n) (q.relabel j)
      (w.relabel j) (r.relabel j) ⟨symm same⟩ ret
  have atBottom : D B (T :: F.not :: Γ) result := by
    have trueT : D B (T :: F.not :: Γ) T := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := held
    apply nodeAtCases 3 1 0 ![q,w,r] result (onTape bottomTest 0 (suc z) ![q,w,r] trueT)
    intro β j Δ fields keep count shape _
    rcases fields with _ | ⟨t,_ | ⟨d,ds⟩⟩ <;> simp at count
    have raw' := renameInto (⟨addHyp (addHyp h F.not) T⟩ :
      D B (T :: F.not :: Γ) (programGraph raw (suc z) ![ctx,ty,q,w,r])) j Δ keep
    simp only [programRename,fiveRename,sucRelabel,zRelabel] at raw'
    have toAtom := replaceRawSource raw (ctx.relabel j) (ty.relabel j) (q.relabel j) (bottomTerm t)
      (w.relabel j) (r.relabel j) shape raw'
    obtain ⟨no⟩ := atoms.bottom B β Δ (ctx.relabel j) (ty.relabel j)
      t (w.relabel j) (r.relabel j) toAtom
    exact ⟨Derivation.explosion no⟩
  have ordinary : D B (T.not :: F.not :: Γ) result := by
    have f : D B (T.not :: F.not :: Γ) F.not := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have t : D B (T.not :: F.not :: Γ) T.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := held
    exact exact_OpenLiteralGuardedRawNonAtom raw ![ctx,ty,q,w,r] ⟨addHyp (addHyp h F.not) T.not⟩
      (nodeZero 0 2 q f) (nodeZero 3 1 q t)
  obtain ⟨fa⟩ := atFree
  obtain ⟨bo⟩ := atBottom
  obtain ⟨ord⟩ := ordinary
  have neither : Derivation B (F.not :: Γ) result :=
    disjunctionElimination (excludedMiddle T) (Derivation.implicationIntroduction bo) (Derivation.implicationIntroduction ord)
  exact ⟨disjunctionElimination (excludedMiddle F)
    (Derivation.implicationIntroduction fa) (Derivation.implicationIntroduction neither)⟩

theorem exact_OpenLiteralAtomicTypedGuardReturn (p other W : Program 3) (V : Program 1)
    (ctx ty q w r : OTerm α)
    (held : D B Γ (programGraph (atomicTypedRaw p other W V) (suc z) ![ctx,ty,q,w,r])) :
    D B Γ (programGraph (guardedRaw (atomicTypedRaw p other W V)) (suc z) ![ctx,ty,q,w,r]) :=
  exact_OpenLiteralRawGuardReturnFromAtoms (atomicTypedRaw p other W V)
    ⟨fun B α Γ => exact_OpenLiteralAtomicTypedFreeTarget p other W V,
     fun B α Γ => exact_OpenLiteralAtomicTypedBottomReject p other W V⟩ ctx ty q w r held

#print axioms exact_OpenLiteralRawGuardReturnFromAtoms
#print axioms exact_OpenLiteralAtomicTypedGuardReturn
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTypedGuardReturnProof
