module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.TickProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.IterationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
def tickTag (tag : Nat) : Nat := tag + stepTag (.projection (0 : Fin 2)) + 1
theorem tickInstalled {n : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) :
 (nodes p)[tickTag tag]? = some ⟨2,tick⟩ := by
 have hs := Equations.recursionStepChild p tag (.projection (0 : Fin 2))
  (applyTwo tick (.projection 1) (.projection 3)) ht
 exact Equations.functionChild p _ tick
  (Fin.cases (.projection (1 : Fin 4)) (Fin.cases (.projection (3 : Fin 4)) Fin.elim0)) hs
theorem zero {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) (state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iterateCall tag .zero state raw) state)) := by
 have hb := GorbowPRSubtree.Proof.lookupTransport n p tag ⟨3,iterator⟩ 1
  ⟨2,.projection (0 : Fin 2)⟩ ht
  (GorbowPRChildTags.Proof.recursionBase 2 (.projection (0 : Fin 2))
   (applyTwo tick (.projection 1) (.projection 3)))
 obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 2
  (.projection (0 : Fin 2)) (applyTwo tick (.projection 1) (.projection 3)) ht ctx (state ::ᵥ raw ::ᵥ nil)
 obtain ⟨hp⟩ := Equations.projection p (tag+1) (0 : Fin 2) hb (state ::ᵥ raw ::ᵥ nil)
 exact ⟨Logic.trans _ _ _ hz hp⟩
theorem successor {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) (count state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iterateCall tag (.succ count) state raw)
   (call (tickTag tag) (iterateCall tag count state raw ::ᵥ raw ::ᵥ nil)))) := by
 let g : Fin 2 → Program 4 := Fin.cases (.projection 1) (Fin.cases (.projection 3) Fin.elim0)
 have hs := Equations.recursionStepChild p tag (.projection (0 : Fin 2))
  (applyTwo tick (.projection 1) (.projection 3)) ht
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 2
  (.projection (0 : Fin 2)) (applyTwo tick (.projection 1) (.projection 3)) ht ctx count (state ::ᵥ raw ::ᵥ nil)
 obtain ⟨hc⟩ := Equations.compositionProjections p
  (tag + stepTag (.projection (0 : Fin 2))) tick g hs
  (Fin.cases (1 : Fin 4) (Fin.cases (3 : Fin 4) Fin.elim0))
  (fun i => by cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i)
  (count ::ᵥ iterateCall tag count state raw ::ᵥ state ::ᵥ raw ::ᵥ nil)
 have hv : List.Vector.ofFn (fun i =>
  (count ::ᵥ iterateCall tag count state raw ::ᵥ state ::ᵥ raw ::ᵥ nil).get
   (Fin.cases (1 : Fin 4) (Fin.cases (3 : Fin 4) Fin.elim0) i)) =
  iterateCall tag count state raw ::ᵥ raw ::ᵥ nil := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
 rw [hv] at hc
 exact ⟨Logic.trans _ _ _ hr hc⟩
theorem tickCongruence {ctx : Nat} {T : Sentence → Prop} tag (a b raw : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (call tag (a ::ᵥ raw ::ᵥ nil)) (call tag (b ::ᵥ raw ::ᵥ nil))) := by
 apply Hilbert.Local.finish
 apply callCongruence (T := T) (G := []) tag _ _
 intro i
 cases i using Fin.cases with
 | zero => exact .base h
 | succ i => cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive raw))
   | succ i => exact Fin.elim0 i
/-- External induction here is over a fixed finite token count, not an assumed
native image of an arbitrary runtime count or encoded input list. -/
theorem firstNumeral {n ctx : Nat} (p : Program n) tag
 (ht : (nodes p)[tag]? = some ⟨3,iterator⟩) (count : Nat) (state raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (iterateCall tag (Term.numeral count.succ) state raw)
   (iterateCall tag (Term.numeral count) (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw))) := by
 induction count with
 | zero =>
  obtain ⟨hs⟩ := successor p tag ht .zero state raw
  obtain ⟨hz⟩ := zero p tag ht state raw
  obtain ⟨hr⟩ := zero p tag ht (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw
  exact ⟨Logic.trans _ _ _ hs (Logic.trans _ _ _ (tickCongruence _ _ _ raw hz)
   (Support.equalitySymmetry _ _ hr))⟩
 | succ count ih =>
  obtain ⟨hl⟩ := successor p tag ht (Term.numeral count.succ) state raw
  obtain ⟨hr⟩ := successor p tag ht (Term.numeral count) (call (tickTag tag) (state ::ᵥ raw ::ᵥ nil)) raw
  obtain ⟨hi⟩ := ih
  exact ⟨Logic.trans _ _ _ hl (Logic.trans _ _ _ (tickCongruence _ _ _ raw hi)
   (Support.equalitySymmetry _ _ hr))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.IterationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.IterationProof
