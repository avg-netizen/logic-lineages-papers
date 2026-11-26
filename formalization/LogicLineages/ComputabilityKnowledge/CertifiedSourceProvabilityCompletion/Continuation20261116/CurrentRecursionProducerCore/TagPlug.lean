module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagPlug
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph

def appendRaw {ctx inputs : Nat} (raw : List.Vector (Term ctx) inputs) (code : Term ctx) : List.Vector (Term ctx) (inputs+1) :=
 List.Vector.ofFn (Fin.lastCases code raw.get)
def tagEnvironment {n depth inputs : Nat} (e : Environment n depth inputs) : Environment (n+1) depth (inputs+1) :=
 Fin.lastCases (.inr (Fin.last inputs)) (fun i => match e i with | .inl j => .inl j | .inr j => .inr j.castSucc)

theorem variableValue {n depth inputs ctx : Nat} (ctag atag : Nat) (e : Environment n depth inputs)
 (raw : List.Vector (Term ctx) inputs) (code : Term ctx) (i : Fin n) :
 termValue ctag atag (tagEnvironment e) (appendRaw raw code) (.var i.castSucc) = termValue ctag atag e raw (.var i) := by
 simp only [termValue,tagEnvironment,Fin.lastCases_castSucc]
 cases he : e i with
 | inl j => rfl
 | inr j => simp only [appendRaw,List.Vector.get_ofFn,Fin.lastCases_castSucc]

theorem lastVariable {n depth inputs ctx : Nat} (ctag atag : Nat) (e : Environment n depth inputs)
 (raw : List.Vector (Term ctx) inputs) (code : Term ctx) :
 termValue ctag atag (tagEnvironment e) (appendRaw raw code) (.var (Fin.last n)) = code := by
 simp only [termValue,tagEnvironment,Fin.lastCases_last,appendRaw,List.Vector.get_ofFn,Fin.lastCases_last]

theorem termPlug {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (code : Term ctx) (tag : Nat)
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (rawNumeral (Term.numeral tag))))
 (t : Term (n+1)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag (tagEnvironment e) (appendRaw raw code) t)
   (termValue ctag atag e raw (substitute (CurrentRecursionBaseProgram.TagSyntax.plug n tag) t)))) := by
 apply TermSubstitution.substitution p ctag atag hc ha _ _ _ _ _ ?_ t
 intro i
 refine Fin.lastCases ?_ (fun j => ?_) i
 · obtain ⟨hn⟩ := CurrentCompositionCertificate.CallEncodingProof.numeral p ctag atag hc e raw tag
   rw [CurrentRecursionBaseProgram.TagSyntax.plugLast,lastVariable]
   exact ⟨Logic.trans _ _ _ hcode (Support.equalitySymmetry _ _ hn)⟩
 · rw [CurrentRecursionBaseProgram.TagSyntax.plugCast,variableValue]
   exact ⟨.logical (.reflexive _)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagPlug
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagPlug
