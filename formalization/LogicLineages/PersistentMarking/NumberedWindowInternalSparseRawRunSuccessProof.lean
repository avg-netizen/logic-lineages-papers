module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunShapeOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename compositionValue outputTransport headTransport valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn bindTerm liftBind varBind eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans congTerm sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (ownState ownRun)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateRename stateSubst)
open NumberedWindowInternalSparseRawRunShapeLogicProof (goodCases)
open NumberedWindowInternalSparseRawRunShapeOwnProof (ownShape)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual head read of the literal two-field scratch. -/
theorem headRead (a b : OTerm α) :
    Nonempty (Derivation body Γ (programGraph cellHead a ![stateTerm a b])) := by
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) a (rawCons b z)
  exact ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩

/-- Ordinary equality congruence of the scratch term in both fields. -/
theorem stateCongr (a a' b b' : OTerm α)
    (ha : Nonempty (Derivation body Γ (eqn a a')))
    (hb : Nonempty (Derivation body Γ (eqn b b'))) :
    Nonempty (Derivation body Γ (eqn (stateTerm a b) (stateTerm a' b'))) := by
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  have first := congTerm (stateTerm (.var (.inr 0)) (b.relabel Sum.inl)) da
  simp only [stateSubst,varBind,liftBind] at first
  have second := congTerm (stateTerm (a'.relabel Sum.inl) (.var (.inr 0))) db
  simp only [stateSubst,varBind,liftBind] at second
  exact ⟨trans first second⟩

/-- A supplied own state whose actual head read is a successor is the
terminal scratch: the reachable shape excludes the zero-flag disjunct
by the original successor-not-zero axiom, leaving frame zero. -/
theorem successTerminal (p other : Program 3) (k st : OTerm α) (xs : Fin 3 → OTerm α)
    (hhead : Nonempty (Derivation body Γ (programGraph cellHead (suc k) ![st])))
    (hown : Nonempty (Derivation body Γ (programGraph (ownState p other) st xs))) :
    Nonempty (Derivation body Γ (eqn st (stateTerm (suc k) z))) := by
  apply goodCases Γ st _ (ownShape p other st xs hown)
  intro β j Δ a b hj he hd
  rw [eqnRelabel,stateRename,sucRelabel,zRelabel]
  have hhead' := renameInto hhead j Δ hj
  rw [programRename,inputsRename,sucRelabel] at hhead'
  have moved := headTransport cellHead (suc (k.relabel j)) (st.relabel j) (stateTerm a b) ![]
    he hhead'
  obtain ⟨flag⟩ := valueUnique cellHead (suc (k.relabel j)) a ![stateTerm a b] moved
    (headRead a b)
  obtain ⟨de⟩ := he
  obtain ⟨dd⟩ := hd
  have zeroFlag : Derivation body Δ
      ((eqn a z).imp (eqn (st.relabel j) (stateTerm (suc (k.relabel j)) z))) :=
    Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply
      (trans (addHyp flag _) (Derivation.hypothesis List.mem_cons_self))))
  obtain ⟨cong⟩ := stateCongr (body := body) (Γ := eqn b z :: Δ) a (suc (k.relabel j)) b z
    ⟨symm (addHyp flag _)⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have zeroFrame : Derivation body Δ
      ((eqn b z).imp (eqn (st.relabel j) (stateTerm (suc (k.relabel j)) z))) :=
    Derivation.implicationIntroduction (trans (addHyp de _) cong)
  exact ⟨disjunctionElimination dd zeroFlag zeroFrame⟩

theorem ownRunTerminal (p other : Program 3) (k : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (ownRun p other) (suc k) xs))) :
    Nonempty (Derivation body Γ (programGraph (ownState p other) (stateTerm (suc k) z) xs)) := by
  apply programCompositionCases cellHead (fun _ : Fin 1 => ownState p other) (suc k) xs _ h
  intro β j ys Δ _ hf hg
  rw [programRename,stateRename,sucRelabel,zRelabel]
  rw [sucRelabel] at hf
  have eta : ys = ![ys 0] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [eta] at hf
  have e := successTerminal p other (k.relabel j) (ys 0) (fun a => (xs a).relabel j) hf (hg 0)
  exact outputTransport (ownState p other) (ys 0) (stateTerm (suc (k.relabel j)) z)
    (fun a => (xs a).relabel j) e (hg 0)

theorem terminalOwnRun (p other : Program 3) (k : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (ownState p other) (stateTerm (suc k) z) xs))) :
    Nonempty (Derivation body Γ (programGraph (ownRun p other) (suc k) xs)) := by
  apply compositionValue cellHead (fun _ : Fin 1 => ownState p other) (suc k) xs
    ![stateTerm (suc k) z] (headRead (suc k) z)
  intro i
  obtain rfl := Fin.eq_zero i
  exact h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunSuccessProof
