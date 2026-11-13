module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.InnerRangeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.OuterRangeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds HistoryBounds.SupportProof
open HistoryCancellation.MonotonicityProof HistoryDecoder.OuterEquationsProof

theorem outerZero {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryDecoder.outer true⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (outerCall tag .zero code) .zero)) := by
  have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,HistoryDecoder.outer true⟩ 1 ⟨1,zeroProgram 1⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 (zeroProgram 1) (HistoryDecoder.outerStep true))
  have hf := SixSol20261112.Fuel.Equations.functionChild p (tag+1) .zero Fin.elim0 hb
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 (zeroProgram 1) (HistoryDecoder.outerStep true) ht ctx (code ::ᵥ nil)
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p (tag+1) .zero Fin.elim0 hb (code ::ᵥ nil) nil (fun i => Fin.elim0 i)
  obtain ⟨hzero⟩ := Support.intoRegistry p .zero (tag+1+1) hf _ (NamedArithmeticGraph.Equations.zero (tag+1+1) ctx)
  exact ⟨Logic.trans _ _ _ hz (Logic.trans _ _ _ hc hzero)⟩

def template {ctx : Nat} (tag : Nat) (code : Term ctx) : Formula (ctx+1) :=
  weakBound (outerCall tag (.var 0) (liftTerm code)) (liftTerm code)

theorem templateAt {ctx : Nat} tag (code count : Term ctx) :
    GorbowStandardInstances.instantiate (template tag code) count = weakBound (outerCall tag count code) code := by
  simp only [GorbowStandardInstances.instantiate,template,substWeak,substOuter,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem outerRange {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryDecoder.outer true⟩) (count code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (weakBound (outerCall tag count code) code)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag code
  obtain ⟨hz⟩ := outerZero p tag ht code
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi = template tag code from rfl,templateAt]
    exact .mp (.mp (weakChildTransport _ _ _) hz) (HistoryCancellation.OrderSupportProof.weakZero code)
  let C := liftTerm code
  let x : Term (ctx+1) := .var 0
  have hi : Hilbert.Local T (ctx+1) [phi] (weakBound (outerCall tag x C) C) := .hypothesis List.mem_cons_self
  obtain ⟨hinner⟩ := InnerRangeProof.innerCompleteRange p (outerInnerTag tag) (innerInstalled p tag true ht) x C (outerCall tag x C)
  obtain ⟨he⟩ := outerSuccessor p tag true ht x C
  have hout := Hilbert.Local.mp (.mp (.base (weakChildTransport _ _ _)) (.base he)) (.mp (.base hinner) hi)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substWeak,substOuter,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi count (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi = template tag code from rfl,templateAt] at h
  exact ⟨h⟩

theorem internalRightDecoderBound : Targets.InternalRightDecoderBound := by
  intro n p tag ht ctx input
  have ho := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.outer true) HistoryDecoder.decoderArguments ht
  obtain ⟨he⟩ := decoderEquation p tag true ht input
  obtain ⟨hb⟩ := outerRange p (tag+1) ho (.succ input) input
  exact ⟨.mp (.mp (weakChildTransport _ _ _) he) hb⟩

theorem internalPositiveTailBound : Targets.InternalPositiveTailBound := by
  intro n p tag ht ctx input
  have hd := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => HistoryCodec.predecessor) ht
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder true) (fun _ : Fin 1 => HistoryCodec.predecessor) ht 0
  obtain ⟨he⟩ := HistoryLookup.DestructorProof.destructorEquation p tag true ht (.succ input)
  obtain ⟨hpred⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p (HistoryLookup.DestructorProof.predTag true tag) hp ctx input
  have hcall := Logic.trans _ _ _ he (HistoryLookup.DestructorProof.unaryCallCongruence (tag+1) _ _ hpred)
  obtain ⟨hb⟩ := internalRightDecoderBound n p (tag+1) hd ctx input
  exact ⟨.mp (.mp (weakChildTransport _ _ _) hcall) hb⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoderBounds.OuterRangeProof
