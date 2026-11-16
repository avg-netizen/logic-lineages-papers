module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaPlug
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagRuntime
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open TagPlug

theorem runtime (n : Nat) : tagEnvironment (PrescribedRuntimeSpecialization.runtimeEnvironment n) =
 PrescribedRuntimeSpecialization.runtimeEnvironment (n+1) := by
 funext i
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [tagEnvironment,Fin.lastCases_last,PrescribedRuntimeSpecialization.runtimeEnvironment]
 · simp only [tagEnvironment,Fin.lastCases_castSucc,PrescribedRuntimeSpecialization.runtimeEnvironment]

theorem head (n : Nat) : tagEnvironment (PrescribedRuntimeSpecialization.headEnvironment n) =
 PrescribedRuntimeSpecialization.headEnvironment (n+1) := by
 have h := TagEnvironment.lift (PrescribedRuntimeSpecialization.runtimeEnvironment n)
 rw [runtime] at h
 exact h.symm

theorem rawValues {ctx m : Nat} (J : CurrentRecursionBaseProgram.Tags) (target : Term ctx) (inputs : List.Vector (Term ctx) m) :
 appendRaw (inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)) (LiteralNumeralPrefix.numeralCall J.ntag target) =
 CurrentRecursionBaseProgram.rawValues J target inputs := by
 ext i
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [appendRaw,CurrentRecursionBaseProgram.rawValues,List.Vector.get_ofFn,Fin.lastCases_last]
 · simp only [appendRaw,CurrentRecursionBaseProgram.rawValues,List.Vector.get_ofFn,Fin.lastCases_castSucc,List.Vector.get_map]

theorem rawHead {ctx n : Nat} (raw : List.Vector (Term ctx) (n+1)) (code : Term ctx) :
 (appendRaw raw code).head = raw.head := by
 change (appendRaw raw code).get ((0 : Fin (n+1)).castSucc) = raw.head
 simp only [appendRaw,List.Vector.get_ofFn,Fin.lastCases_castSucc,List.Vector.get_zero]

theorem rawTail {ctx n : Nat} (raw : List.Vector (Term ctx) (n+1)) (code : Term ctx) :
 (appendRaw raw code).tail = appendRaw raw.tail code := by
 ext i
 rw [List.Vector.get_tail_succ]
 refine Fin.lastCases ?_ (fun j => ?_) i
 · have hi : (Fin.last n).succ = Fin.last (n+1) := by apply Fin.ext; rfl
   rw [hi]
   simp only [appendRaw,List.Vector.get_ofFn,Fin.lastCases_last]
 · have hi : j.castSucc.succ = j.succ.castSucc := by apply Fin.ext; rfl
   rw [hi]
   simp only [appendRaw,List.Vector.get_ofFn,Fin.lastCases_castSucc,List.Vector.get_tail_succ]

theorem formula {arity n ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) n) (code : Term ctx) (tag : Nat)
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (rawNumeral (Term.numeral tag))))
 (f : Formula (n+1)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (appendRaw raw code) f (PrescribedRuntimeSpecialization.runtimeEnvironment (n+1)))
   (formulaValue ctag atag raw (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug n tag) f)
    (PrescribedRuntimeSpecialization.runtimeEnvironment n)))) := by
 have h := FormulaPlug.formulaPlug p ctag atag hc ha raw code tag hcode (PrescribedRuntimeSpecialization.runtimeEnvironment n) f
 rw [runtime] at h
 exact h

theorem headFormula {arity n ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) n) (code : Term ctx) (tag : Nat)
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (rawNumeral (Term.numeral tag))))
 (f : Formula (n+2)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (appendRaw raw code) f (PrescribedRuntimeSpecialization.headEnvironment (n+1)))
   (formulaValue ctag atag raw (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (n+1) tag) f)
    (PrescribedRuntimeSpecialization.headEnvironment n)))) := by
 have h := FormulaPlug.formulaPlug p ctag atag hc ha raw code tag hcode (PrescribedRuntimeSpecialization.headEnvironment n) f
 rw [head] at h
 exact h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagRuntime
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagRuntime
