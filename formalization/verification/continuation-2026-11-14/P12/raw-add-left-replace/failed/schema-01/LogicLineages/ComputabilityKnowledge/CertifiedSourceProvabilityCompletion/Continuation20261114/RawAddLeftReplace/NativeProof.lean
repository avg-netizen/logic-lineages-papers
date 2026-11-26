module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof
open HistoryDispatcher.NativeProof (encodeProd encodeNat)
open TwoSol20261113.ReflexivityRecognizer
open TwoSol20261113.ReflexivityRecognizer.NativeProof
theorem lineEval {n : Nat} (left right fixed : Program n) (v : List.Vector Nat n) (a b c : List Nat)
 (ha : evaluate left v = Encodable.encode a) (hb : evaluate right v = Encodable.encode b) (hc0 : evaluate fixed v = Encodable.encode c) :
 evaluate (line left right fixed) v = Encodable.encode (RawAddLeftReplace.nativeLine a b c) := by
 have hp (a b : Nat) : evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) = Nat.pair a b := HistoryCodec.NativeProof.nativePair _
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ := HistoryCodec.NativeProof.nativeConsAllVectors _
 have hvar : evaluate (variableRaw n) v = Encodable.encode ([0,0] : List Nat) := by
  simp only [variableRaw,twoEval,constantEval,hc]
  rfl
 have hav := RawSuccReplace.NativeProof.binaryEval 3 _ _ v _ _ hc0 ha
 have hbv := RawSuccReplace.NativeProof.binaryEval 3 _ _ v _ _ hc0 hb
 have hxv := RawSuccReplace.NativeProof.binaryEval 3 _ _ v _ _ hc0 hvar
 have ht : evaluate (templateRaw left fixed) v = Encodable.encode (nativeTemplate a c) :=
  RawSuccReplace.NativeProof.binaryEval 0 _ _ v _ _ hav hxv
 have he := RawSuccReplace.NativeProof.binaryEval 0 _ _ v _ _ ha hb
 have hself := RawSuccReplace.NativeProof.binaryEval 0 _ _ v _ _ hav hav
 have hcong := RawSuccReplace.NativeProof.binaryEval 0 _ _ v _ _ hav hbv
 have himp := RawSuccReplace.NativeProof.binaryEval 7 _ _ v _ _ hself hcong
 have hformula : evaluate (formulaRaw left right fixed) v = Encodable.encode (nativeFormula a b c) :=
  RawSuccReplace.NativeProof.binaryEval 7 _ _ v _ _ he himp
 have hnil : Encodable.encode ([] : List (List Nat)) = 0 := rfl
 simp only [line,twoEval,constantEval,ha,hb,ht,hformula,hp,hc,nativeLine,encodeProd,
  encodeNat,HistoryLookup.NativeProof.encodeCons,hnil]

theorem nativeLine : Targets.NativeLine := by
 intro a b c
 exact lineEval (.projection 0) (.projection 1) (.projection 2) (Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ Encodable.encode c ::ᵥ nil) a b c rfl rfl rfl

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

theorem rawLineAccepted (a b c : List Nat)
 (ha : GorbowSyntaxValidation.validTerm 0 a = true) (hb : GorbowSyntaxValidation.validTerm 0 b = true) (hc0 : GorbowSyntaxValidation.validTerm 0 c = true) :
 HistoryDispatcher.logicalFunction (Encodable.encode (RawAddLeftReplace.nativeLine a b c) ::ᵥ nil) = 1 := by
 have hg : GorbowLogicalAxiomCode.guardTerms 0 2 [a,b] = true := by
  simp [GorbowLogicalAxiomCode.guardTerms,ha,hb]
 have hall := (GorbowLogicalAxiomCodeProof.guardCalibration.2 0 2 [a,b]).mp hg
 obtain ⟨t,ht⟩ := hall.2 a (by simp)
 obtain ⟨u,hu⟩ := hall.2 b (by simp)
 have hgc : GorbowLogicalAxiomCode.guardTerms 0 1 [c] = true := by
  simp [GorbowLogicalAxiomCode.guardTerms,hc0]
 obtain ⟨w,hw⟩ := ((GorbowLogicalAxiomCodeProof.guardCalibration.2 0 1 [c]).mp hgc).2 c (by simp)
 subst a; subst b; subst c
 let phi : Formula 1 := .equal
  (.add (GorbowStandardInstances.closedTermInContext 1 w) (GorbowStandardInstances.closedTermInContext 1 t))
  (.add (GorbowStandardInstances.closedTermInContext 1 w) (.var 0))
 have hc : GorbowLogicalAxiomCode.compile 0 (12,[nativeTemplate (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode w),
  GorbowTermPrefixCode.encode t,GorbowTermPrefixCode.encode u]) =
  some (nativeFormula (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) (GorbowTermPrefixCode.encode w)) := by
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
  GorbowProofChecker.rule,GorbowProofChecker.payload,RawAddLeftReplace.nativeLine,HistoryDispatcher.truth,hc]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof.nativeLine
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddLeftReplace.NativeProof.rawLineAccepted
