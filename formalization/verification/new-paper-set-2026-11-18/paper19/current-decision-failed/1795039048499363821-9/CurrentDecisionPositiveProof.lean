module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeProof
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceProof
public import LogicLineages.OrdinalComparison.WWEncodedComparisonProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecision

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open GroundEquivalence ParametricSourceSuccessor ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem positive_denotation (f : Nat → Nat) {Γ}
    (e : OrdinalExpression Γ) (c : ClosedPositive) (h : extractPositive e = some c)
    (ν : OrdinalComponent Γ → Ordinal) : denoteWith f ν e = denote ν e := by
  induction e generalizing c with
  | var x => simp [extractPositive] at h
  | zero => simp [extractPositive] at h
  | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb =>
    cases ha : extractPositive a with
    | none => simp [extractPositive,ha] at h
    | some aa =>
      cases hb : extractPositive b with
      | none => simp [extractPositive,ha,hb] at h
      | some bb => simp only [denoteWith, denote, iha aa ha, ihb bb hb]
  | collapse a b => simp [extractPositive] at h

private theorem closed_coordinates (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ τ}
    (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : AdmissibleAssignment.assignment p d.term = some v) :
    ∃ a : List NONote,
      compiledPositive p (RawSourceDAG.encode ⟨Γ,τ,d⟩) = normalCodes a ∧
      ∀ ρ j, positiveNoteAt a j = CurrentCounterBound.coordinate f v ρ (j+1) := by
  obtain ⟨v',c,hv',hc,hcode,hclosed,_,_,_⟩ := PolicySourceInterfaceProof.typed p Γ hg τ d.term
  rw [hv] at hv'
  cases Option.some.inj hv'
  refine ⟨c.positiveNotes, ?_, ?_⟩
  · unfold compiledPositive
    rw [CurrentTreeCode.exactExpansion Γ τ d]
    have hlen : (RawSourceDAG.encode ⟨Γ,τ,d⟩).1.length = Γ.length := List.length_map _
    rw [hlen, hcode]
    simp only [Option.getD_some, CompiledVector.syntaxCode, CompiledVector.positiveNotes, normalCodes,
      List.map_ofFn, Function.comp_def, encodedClosedPositiveCorrect]
  · intro ρ j
    by_cases hj : j < τ.level
    · let ix : Fin τ.level := ⟨j,hj⟩
      have hsu : j+1 < τ.level+1 := Nat.succ_lt_succ hj
      have orig := compiledVectorSound Γ τ.level v c hc ρ ix.succ
      obtain ⟨_,z,hz,_,_,_⟩ := hclosed ix.succ (Nat.succ_pos _)
      have eq := positive_denotation f (v ix.succ) z hz (fun x => (ρ x : Ordinal))
      change (c.positive ix).evaluate.1.repr = _ at orig
      simp only [positiveNoteAt, CompiledVector.positiveNotes, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dif_pos hj, Option.getD_some, CurrentCounterBound.coordinate,
        ordinalVectorAt, dif_pos hsu]
      exact orig.trans eq.symm
    · simp only [positiveNoteAt, CompiledVector.positiveNotes, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dif_neg hj, Option.getD_none, CurrentCounterBound.coordinate,
        ordinalVectorAt, dif_neg (show ¬ j+1 < τ.level+1 by omega), zeroNote, denoteWith]
      rfl

theorem positive_correct (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ σ τ}
    (hg : ∀ t ∈ Γ, t = Ty.ground) (strict : Bool) (a : Input Γ σ) (b : Input Γ τ)
    (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level)
    (ha : AdmissibleAssignment.assignment p a.term = some av)
    (hb : AdmissibleAssignment.assignment p b.term = some bv) (ρ : OrdinalComponent Γ → Nat) :
    positiveTest p (strict,RawSourceDAG.encode ⟨Γ,σ,a⟩,RawSourceDAG.encode ⟨Γ,τ,b⟩) = true ↔
      ∀ j, CurrentCounterBound.coordinate f av ρ (j+1) ≤ CurrentCounterBound.coordinate f bv ρ (j+1) := by
  obtain ⟨an,ac,ae⟩ := closed_coordinates p f hg a av ha
  obtain ⟨bn,bc,be⟩ := closed_coordinates p f hg b bv hb
  unfold positiveTest
  dsimp only
  rw [ac,bc,positiveComparisonSourceCorrect]
  simp only [ae,be]

theorem positive_computable (p : AdmissibleSum.Policy) (hp : PolicyShape.Effective p) :
    Computable (positiveTest p) := by
  have he : Computable (fun p' : Nat × Nat => PolicySourceInterface.compile p p'.1 p'.2) :=
    PolicySourceInterfaceProof.programs.1 p hp
  have hc : Computable (fun d : RawSourceDAG.Code =>
      PolicySourceInterface.compile p d.1.length (CurrentTreeCode.expand d)) :=
    he.comp ((Primrec.list_length.comp Primrec.fst).to_comp.pair CurrentTreeCode.effective.to_comp)
  have hg : Computable (fun d : RawSourceDAG.Code =>
      ((PolicySourceInterface.compile p d.1.length (CurrentTreeCode.expand d)).getD (0,[])).2) :=
    Computable.snd.comp (Primrec.option_getD.to_comp.comp hc (Computable.const (0,[])))
  have hn : Primrec (fun l : List Nat => l.map encodedClosedPositive) :=
    Primrec.list_map Primrec.id (encodedClosedPositivePrimitiveRecursive.comp Primrec.snd).to₂
  have hd : Computable (compiledPositive p) := hn.to_comp.comp hg
  exact positiveComparisonPrimitiveRecursive.to_comp.comp
    (hd.comp (Computable.fst.comp Computable.snd)) (hd.comp (Computable.snd.comp Computable.snd))

end LogicLineages.ControlSensitivityCurrent.CurrentDecision
