module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
variable {n arity ctx : Nat} (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x) (args : List.Vector (Term ctx) arity)

theorem bin (k : Nat) (q z : Program arity) (v w : Term ctx)
 (hq : Computes p [] q args v) (hz : Computes p [] z args w) :
 Computes p [] (RawSuccReplace.binaryRaw k q z) args (RawSuccReplace.binaryValue I.ctag I.atag k v w) := by
 have happ := binary p [] args HistoryAppend.append q z v w _ hq hz
  (copies p [] HistoryAppend.append I.atag I.ha (v ::ᵥ w ::ᵥ nil))
 exact binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args k) happ (copies p [] HistoryCodec.cons I.ctag I.hc _)

theorem succ (q : Program arity) (v : Term ctx) (hq : Computes p [] q args v) :
 Computes p [] (RawAddSucc.successorRaw q) args (RawAdditionComputation.succRaw I.ctag v) :=
 binary p [] args HistoryCodec.cons _ _ _ _ _ (constantValue p [] args 2) hq (copies p [] HistoryCodec.cons I.ctag I.hc _)

theorem single (q : Program arity) (v : Term ctx) (hq : Computes p [] q args v) :
 Computes p [] (singleton q) args (HistoryLookup.consCall I.ctag v .zero) :=
 binary p [] args HistoryCodec.cons _ _ _ _ _ hq (constantValue p [] args 0) (copies p [] HistoryCodec.cons I.ctag I.hc _)

theorem reflexive (q : Program arity) (v : Term ctx) (hq : Computes p [] q args v) :
 Computes p [] (applyOne RawReflexivity.lineConstructor q) args (RawReflexivity.lineCall I.reflexivityTag v) :=
 unary p [] args RawReflexivity.lineConstructor q v _ hq
  (copies p [] RawReflexivity.lineConstructor I.reflexivityTag I.hreflexivity _)

theorem mpCompute (q i j : Program arity) (v w z : Term ctx)
 (hq : Computes p [] q args v) (hi : Computes p [] i args w) (hj : Computes p [] j args z) :
 Computes p [] (mp q i j) args (LiteralMPRun.certificate I.mpTag .zero v w z) := by
 apply compose p [] LiteralRawMP.constructor
  (Fin.cases (constant arity 0) (Fin.cases q (Fin.cases i (Fin.cases j Fin.elim0))))
  args (.zero ::ᵥ v ::ᵥ w ::ᵥ z ::ᵥ nil) _
 · intro k
   cases k using Fin.cases with
   | zero => exact constantValue p [] args 0
   | succ k => cases k using Fin.cases with
     | zero => exact hq
     | succ k => cases k using Fin.cases with
       | zero => exact hi
       | succ k => cases k using Fin.cases with
         | zero => exact hj
         | succ k => exact Fin.elim0 k
 · exact copies p [] LiteralRawMP.constructor I.mpTag I.hmp _

theorem rightLine (t u v : Program arity) (tv uv vv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv) :
 Computes p [] (RawRightReplace.line t u v) args (RawRightReplace.lineCall I.qtag tv uv vv) := by
 have h := RawRightReplace.ConstructorProof.computesLine p [] I.ptag I.ctag I.atag I.hp I.hc I.ha args t u v tv uv vv ht hu hv
 obtain ⟨he⟩ := RawRightReplace.StatementChecks.exactInternalLine n p I.qtag I.ptag I.ctag I.atag I.hq I.hp I.hc I.ha ctx tv uv vv
 intro tag hh
 obtain ⟨hc⟩ := h tag hh
 exact ⟨localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ he))⟩

theorem replaceLine (t u : Program arity) (tv uv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) :
 Computes p [] (RawSuccReplace.line t u) args (RawSuccReplace.lineCall I.replaceTag tv uv) := by
 have h := RawSuccReplace.ConstructorProof.computesLine p [] I.ptag I.ctag I.atag I.hp I.hc I.ha args t u tv uv ht hu
 obtain ⟨he⟩ := RawSuccReplace.StatementChecks.exactInternalLine n p I.replaceTag I.ptag I.ctag I.atag I.hreplace I.hp I.hc I.ha ctx tv uv
 intro tag hh
 obtain ⟨hc⟩ := h tag hh
 exact ⟨localTrans _ _ _ hc (.base (Support.equalitySymmetry _ _ he))⟩

theorem transportCompute (t u v first second : Program arity) (tv uv vv f s : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv)
 (hf : Computes p [] first args f) (hs : Computes p [] second args s) :
 Computes p [] (transport t u v first second) args (RawEqualityComposition.transportCertificate I.mpTag I.qtag I.ctag I.atag tv uv vv f s) := by
 have ho := bin p old a x I args 0 _ _ _ _ hu hv
 have hi := bin p old a x I args 7 _ _ _ _ (bin p old a x I args 0 _ _ _ _ ht hv) ho
 have hr := single p old a x I args _ _ (rightLine p old a x I args _ _ _ _ _ _ ht hu hv)
 exact mpCompute p old a x I args _ _ _ _ _ _ ho (mpCompute p old a x I args _ _ _ _ _ _ hi hr hf) hs

theorem symmetryCompute (t u cert : Program arity) (tv uv cv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hc : Computes p [] cert args cv) :
 Computes p [] (symmetry t u cert) args (RawEqualityComposition.symmetryCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag tv uv cv) :=
 transportCompute p old a x I args _ _ _ _ _ _ _ _ _ _ ht hu ht hc
  (single p old a x I args _ _ (reflexive p old a x I args _ _ ht))

theorem transitivityCompute (t u v first second : Program arity) (tv uv vv f s : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hv : Computes p [] v args vv)
 (hf : Computes p [] first args f) (hs : Computes p [] second args s) :
 Computes p [] (transitivity t u v first second) args (RawEqualityComposition.transitivityCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag tv uv vv f s) :=
 transportCompute p old a x I args _ _ _ _ _ _ _ _ _ _ hu ht hv (symmetryCompute p old a x I args _ _ _ _ _ _ ht hu hf) hs

theorem congruenceCompute (t u cert : Program arity) (tv uv cv : Term ctx)
 (ht : Computes p [] t args tv) (hu : Computes p [] u args uv) (hc : Computes p [] cert args cv) :
 Computes p [] (congruence t u cert) args (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag tv uv cv) := by
 have st := succ p old a x I args _ _ ht
 have su := succ p old a x I args _ _ hu
 have ho := bin p old a x I args 0 _ _ _ _ st su
 have hi := bin p old a x I args 7 _ _ _ _ (bin p old a x I args 0 _ _ _ _ st st) ho
 have hr := single p old a x I args _ _ (replaceLine p old a x I args _ _ _ _ ht hu)
 have hf := single p old a x I args _ _ (reflexive p old a x I args _ _ st)
 exact mpCompute p old a x I args _ _ _ _ _ _ ho (mpCompute p old a x I args _ _ _ _ _ _ hi hr hc) hf

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof.transportCompute
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof.symmetryCompute
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof.transitivityCompute
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.CombinatorProof.congruenceCompute
