module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open TwoSol20261113.ReflexivityRecognizer
open TwoSol20261113.ReflexivityRecognizer.NativeProof
theorem binaryEval {n : Nat} (token : Nat) (left right : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate left v = Encodable.encode a) (hb : evaluate right v = Encodable.encode b) :
 evaluate (binaryRaw token left right) v = Encodable.encode (GorbowCodeConstructors.binary token a b) := by
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 simp only [binaryRaw,twoEval,constantEval,ha,hb,appendList,hc,GorbowCodeConstructors.binary,
  HistoryLookup.NativeProof.encodeCons,encodeNat]

theorem lineEval {n : Nat} (left right : Program n) (v : List.Vector Nat n) (a b : List Nat)
 (ha : evaluate left v = Encodable.encode a) (hb : evaluate right v = Encodable.encode b) :
 evaluate (line left right) v = Encodable.encode (RawSuccReplace.nativeLine a b) := by
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b := HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ := HistoryCodec.NativeProof.nativeConsAllVectors _
 have hsa : evaluate (RawAddSucc.successorRaw left) v = Encodable.encode (2 :: a) := by
  simp only [RawAddSucc.successorRaw,twoEval,constantEval,ha,hc]; rfl
 have hsb : evaluate (RawAddSucc.successorRaw right) v = Encodable.encode (2 :: b) := by
  simp only [RawAddSucc.successorRaw,twoEval,constantEval,hb,hc]; rfl
 have hvar : evaluate (RawAddSucc.successorRaw (applyTwo HistoryCodec.cons (constant n 0)
  (applyTwo HistoryCodec.cons (constant n 0) (constant n 0)))) v = Encodable.encode ([2,0,0] : List Nat) := by
  simp only [RawAddSucc.successorRaw,twoEval,constantEval,hc]; rfl
 have ht : evaluate (templateRaw left) v = Encodable.encode (nativeTemplate a) :=
  binaryEval 0 _ _ v _ _ hsa hvar
 have he := binaryEval 0 _ _ v _ _ ha hb
 have hself := binaryEval 0 _ _ v _ _ hsa hsa
 have hcong := binaryEval 0 _ _ v _ _ hsa hsb
 have himp := binaryEval 7 _ _ v _ _ hself hcong
 have hformula : evaluate (formulaRaw left right) v = Encodable.encode (nativeFormula a b) :=
  binaryEval 7 _ _ v _ _ he himp
 have hnil : Encodable.encode ([] : List (List Nat)) = 0 := rfl
 simp only [line,twoEval,constantEval,ha,hb,ht,hformula,hp,hc,nativeLine,encodeProd,
  encodeNat,HistoryLookup.NativeProof.encodeCons,hnil]

theorem nativeLine : Targets.NativeLine := by
 intro a b
 exact lineEval (.projection 0) (.projection 1) (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ nil) a b rfl rfl

theorem closedEncode (t : Term 0) (n : Nat) :
 GorbowTermPrefixCode.encode (GorbowStandardInstances.closedTermInContext n t) = GorbowTermPrefixCode.encode t := by
 induction t with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => exact congrArg (List.cons 2) ih
 | add t u ht hu => exact congrArg (List.cons 3) (congrArg₂ List.append ht hu)
 | mul t u ht hu => exact congrArg (List.cons 4) (congrArg₂ List.append ht hu)
 | universalFunction t ih => exact congrArg (List.cons 5) ih

theorem closedSubstitute (t : Term 0) (u : Term 0) :
 GorbowSubstitution.substitute (Fin.cases u Term.var) (GorbowStandardInstances.closedTermInContext 1 t) = t := by
 induction t with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => exact congrArg Term.succ ih
 | add t v ht hv => exact congrArg₂ Term.add ht hv
 | mul t v ht hv => exact congrArg₂ Term.mul ht hv
 | universalFunction t ih => exact congrArg Term.universalFunction ih

theorem rawLineAccepted (a b : List Nat)
 (ha : GorbowSyntaxValidation.validTerm 0 a = true) (hb : GorbowSyntaxValidation.validTerm 0 b = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (RawSuccReplace.nativeLine a b) ::ᵥ nil) = 1 := by
 have hg : GorbowLogicalAxiomCode.guardTerms 0 2 [a,b] = true := by
  simp [GorbowLogicalAxiomCode.guardTerms,ha,hb]
 have hall := (GorbowLogicalAxiomCodeProof.guardCalibration.2 0 2 [a,b]).mp hg
 obtain ⟨t,ht⟩ := hall.2 a (by simp)
 obtain ⟨u,hu⟩ := hall.2 b (by simp)
 subst a; subst b
 let phi : Formula 1 := .equal (.succ (GorbowStandardInstances.closedTermInContext 1 t)) (.succ (.var 0))
 have hc : GorbowLogicalAxiomCode.compile 0 (12,[nativeTemplate (GorbowTermPrefixCode.encode t),
  GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u]) =
  some (nativeFormula (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u)) := by
  apply (GorbowLogicalAxiomCodeProof.exactCompilation 0 _ _).mpr
  refine ⟨.equalityReplace phi t u,?_,?_⟩
  · simp [GorbowLogicalAxiomCode.encode,phi,nativeTemplate,GorbowFormulaPrefixCode.encode,
      GorbowTermPrefixCode.encode,closedEncode,GorbowCodeConstructors.binary,GorbowCodeConstructors.unary]
  · simp [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,phi,
      GorbowFormulaSubstitution.substituteFormula,GorbowSubstitution.substitute,
      closedSubstitute,nativeFormula,GorbowFormulaPrefixCode.encode,GorbowTermPrefixCode.encode,
      GorbowCodeConstructors.binary,GorbowCodeConstructors.unary]
 simp [HistoryDispatcher.logicalFunction,HistoryDispatcher.decodedLine,HistoryDispatcher.withRule,
  GorbowProofChecker.ruleCheck,GorbowProofChecker.context,GorbowProofChecker.conclusion,
  GorbowProofChecker.rule,GorbowProofChecker.payload,RawSuccReplace.nativeLine,HistoryDispatcher.truth,hc]

theorem nativeRefinement : Targets.NativeRefinement := by
 intro old hold v
 obtain ⟨a,ha⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate leftTermCode v)
 obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal (evaluate rightTermCode v)
 have hl := lineEval leftTermCode rightTermCode v a b ha.symm hb.symm
 have hv : v = v.head ::ᵥ nil := by
  simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
 have hta : evaluate (applyOne termValidator leftTermCode) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 a) := by
  rw [oneEval,← ha,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 have htb : evaluate (applyOne termValidator rightTermCode) v = HistoryDispatcher.truth (GorbowSyntaxValidation.validTerm 0 b) := by
  rw [oneEval,← hb,TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm]
 simp only [logicalLeaf,chooseEval,recognizer,conjunctionEval,twoEval,projectionEval,List.Vector.get_cons_zero,
  hl,equalEval,hta,htb,constantEval,List.Vector.get_zero]
 by_cases he : v.head = Encodable.encode (RawSuccReplace.nativeLine a b)
 · by_cases hva : GorbowSyntaxValidation.validTerm 0 a = true
   · by_cases hvb : GorbowSyntaxValidation.validTerm 0 b = true
     · have hf : HistoryDispatcher.logicalFunction v = 1 := by
        rw [hv,he]; exact rawLineAccepted a b hva hvb
       simp [he,hva,hvb,HistoryDispatcher.truth,hf]
     · simp [he,hva,hvb,HistoryDispatcher.truth,hold]
   · simp [he,hva,HistoryDispatcher.truth,hold]
 · simp [he,hold]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof.nativeRefinement
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace.NativeProof.rawLineAccepted
