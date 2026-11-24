module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoAuxParentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxChildProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm congTerm trans)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalLiteralSyntaxMemoWindow (window)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRawTransport)
open NumberedWindowInternalLiteralSyntaxMemoAuxParentProof (exact_OpenSyntaxMemoAuxParent)
open NumberedWindowInternalLiteralSyntaxMemoAuxRowProof
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveWindowType (W : Program 3) (ctx a b raw : OTerm α)
    (eq : D B Γ (eqn a b)) (held : D B Γ (windowGraph W ctx a raw)) :
    D B Γ (windowGraph W ctx b raw) := by
  unfold windowGraph programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula W) (suc z)
    ![ctx,a,raw] ![ctx,b,raw] _ held
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun q => Fin.elim0 q) k) j) i
  · change D B Γ (equal ctx ctx); rw [equalEqn]; exact ⟨refl _⟩
  · change D B Γ (equal a b); rw [equalEqn]; exact eq
  · change D B Γ (equal raw raw); rw [equalEqn]; exact ⟨refl _⟩

theorem arrowFieldsEq (d c d' c' : OTerm α)
    (ed : D B Γ (eqn d d')) (ec : D B Γ (eqn c c')) :
    D B Γ (eqn (rawCons d c) (rawCons d' c')) := by
  obtain ⟨u⟩ := ed
  obtain ⟨v⟩ := ec
  have h := congTerm (rawCons (.var (.inr 0)) (c.relabel Sum.inl)) u
  have g := congTerm (rawCons (d'.relabel Sum.inl) (.var (.inr 0))) v
  simp only [rawConsSubst,liftBind,varBind] at h g
  exact ⟨trans h g⟩

/-- The child has the original same physical typed-horizon call, not
just a raw machine flag. The result also keeps the genuine window and
syntax at the unchanged argument. Least/class transport is separate. -/
theorem exact_OpenTypedFunctionChild (root other : Program 3) (base : Program 2) (T V : Program 1)
    (ctx ty q w r dom cod fn arg child dom' cod' dst arg' : OTerm α)
    (parts : Parts B Γ q w r dom cod fn arg child dom' cod' dst arg')
    (parent : D B Γ (liftedEndpointGuards (window base T V) V ctx ty q r))
    (run : D B Γ (bit (ownRun root other) ![fn,child,dst])) :
    D B Γ (programGraph (typedRaw5 root other (window base T V) V)
      (suc z) ![ctx,rawCons dom cod,fn,child,dst] ⊓
      childAtWindow (window base T V) V ctx dom arg) := by
  let W := window base T V
  obtain ⟨p⟩ := parent
  have ends := Derivation.conjunctionRight p
  have qWin := windowRawTransport W ctx ty q (auxiliaryTerm dom cod fn arg)
    parts.source ⟨Derivation.conjunctionLeft ends⟩
  have rWin := windowRawTransport W ctx ty r (auxiliaryTerm dom' cod' dst arg')
    parts.target ⟨Derivation.conjunctionRight ends⟩
  obtain ⟨left⟩ := exact_OpenSyntaxMemoAuxParent base T V ctx ty dom cod fn arg qWin
  obtain ⟨right⟩ := exact_OpenSyntaxMemoAuxParent base T V ctx ty dom' cod' dst arg' rWin
  have l := Derivation.conjunctionRight (Derivation.conjunctionRight left)
  have h := Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight right))
  have f := Derivation.conjunctionLeft l
  obtain ⟨same⟩ := arrowFieldsEq dom cod dom' cod' parts.domEq parts.codEq
  obtain ⟨target⟩ := moveWindowType W ctx (rawCons dom' cod') (rawCons dom cod) dst
    ⟨symm same⟩ ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨d⟩ := run
  obtain ⟨codec⟩ := exact_OpenTypedRaw5 B root other W V α Γ ctx (rawCons dom cod) fn child dst
  have packed := Derivation.implicationElimination (Derivation.conjunctionRight codec)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction
        (Derivation.conjunctionIntroduction (Derivation.conjunctionRight f) (Derivation.conjunctionRight h)) d)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft f) target))
  exact ⟨Derivation.conjunctionIntroduction packed (Derivation.conjunctionRight l)⟩

#print axioms arrowFieldsEq
#print axioms exact_OpenTypedFunctionChild
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxChildProof
