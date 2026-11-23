module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenPaddingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenIntroProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveOutputTargets (args5)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalZeroRankAdvance (zeroOutput)
open NumberedWindowInternalZeroRankAdvanceOpenIntroProof (exact_InstallOpenZeroRankOutput)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedPositiveFoldOpenLoopProof
open NumberedWindowInternalParameterizedPositiveFoldOpenPaddingProof (exact_OpenParameterizedLoopPadding)
open NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof (exact_OpenParameterizedPositiveFromTerminal)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An ordered open prefix identified by its real cursor and actual state,
in the same arithmetic proof context. All rows are original advances;
supply actual zero at each selected raw output rather than reflecting it. -/
inductive OriginalZeroPrefix (B : Positive (Fin 1)) (Γ : List (Formula α))
    (g : Program 1) (raw : Program 5) (L : Program 3) (c ty start cert : OTerm α) :
    OTerm α → OTerm α → OTerm α → OTerm α → Prop where
  | init {state} :
      Nonempty (Derivation B Γ (scratchGraph state cert start)) →
      OriginalZeroPrefix B Γ g raw L c ty start cert z state cert start
  | cons {fuel prior cursor current hop tail next out} :
      OriginalZeroPrefix B Γ g raw L c ty start cert fuel prior cursor current →
      Nonempty (Derivation B Γ (consGraph cursor hop tail)) →
      Nonempty (Derivation B Γ (programGraph (advance raw L) (suc next) ![c,ty,current,hop])) →
      Nonempty (Derivation B Γ (unary g z next)) →
      Nonempty (Derivation B Γ (scratchGraph out tail (suc next))) →
      OriginalZeroPrefix B Γ g raw L c ty start cert (suc fuel) out tail (suc next)

theorem exact_OriginalZeroRankPrefixRun (g : Program 1) (raw : Program 5) (L : Program 3)
    (c ty start cert fuel state cursor current : OTerm α)
    (rows : OriginalZeroPrefix B Γ g raw L c ty start cert fuel state cursor current) :
    Nonempty (Derivation B Γ
      (loopAt (zeroOutput g (advance raw L)) state fuel c ty start cert)) ∧
      Nonempty (Derivation B Γ (scratchGraph state cursor current)) := by
  induction rows with
  | init h => exact ⟨exact_OpenParameterizedLoopStart _ _ c ty start cert h,h⟩
  | @cons fuel prior cursor current hop tail next out _ cell orig rank scratch ih =>
    have specialized := exact_InstallOpenZeroRankOutput g (advance raw L) ![c,ty,current,hop] next orig rank
    exact ⟨exact_OpenParameterizedLoopStep _ out prior fuel c ty start cert cursor current hop tail
      (suc next) ih.1 ih.2 cell specialized scratch,scratch⟩

/-- If the genuine ordered prefix ends at the zero cursor at the same
target, and the original certificate fuel is the used prefix fuel plus
a held arithmetic gap, the actual zero-rank checker accepts that tape. -/
theorem exact_OriginalZeroRankPositiveFromOpenRows (g : Program 1) (raw : Program 5) (L : Program 3)
    (c ty source cert target fuel extra state : OTerm α)
    (rows : OriginalZeroPrefix B Γ g raw L c ty (suc source) cert fuel state z (suc target))
    (gap : Nonempty (Derivation B Γ (eqn (add fuel extra) cert)))
    (certNonempty : Nonempty (Derivation B Γ (eqn cert z).not)) :
    Nonempty (Derivation B Γ
      (programGraph (zeroPositive g raw L) (suc z) (args5 c ty source cert target))) := by
  let A := zeroOutput g (advance raw L)
  obtain ⟨run,done⟩ := exact_OriginalZeroRankPrefixRun g raw L c ty (suc source) cert
    fuel state z (suc target) rows
  have padded := exact_OpenParameterizedLoopPadding A state fuel extra c ty
    (suc source) cert (suc target) run done
  have actual := exact_OpenParameterizedLoopFuelTransport A state (add fuel extra) cert
    c ty (suc source) cert gap padded
  exact exact_OpenParameterizedPositiveFromTerminal A state c ty source cert target actual done certNonempty

#print axioms exact_OriginalZeroRankPrefixRun
#print axioms exact_OriginalZeroRankPositiveFromOpenRows

end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
