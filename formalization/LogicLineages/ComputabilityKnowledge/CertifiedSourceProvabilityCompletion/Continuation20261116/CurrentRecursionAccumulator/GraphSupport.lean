module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.GraphSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem composition {n arity m ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity)
 (f : Program m) (ftag : Nat) (hf : (nodes p)[ftag]? = some ⟨m,f⟩)
 (g : Fin m → Program arity) (values : List.Vector (Term ctx) m)
 (hg : ∀ i, Computes p (g i) args (values.get i)) :
 Computes p (.composition f g) args (call ftag values) := by
 intro tag ht
 obtain ⟨he⟩ := Equations.compositionValues p tag f g ht args values
  (fun i => hg i _ (Equations.argumentChild p tag f g ht i))
 obtain ⟨hc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tag+1) ftag m f
  (Equations.functionChild p tag f g ht) hf ctx values
 exact ⟨Logic.trans _ _ _ he hc⟩

theorem successorProjection {n arity ctx : Nat} (p : Program n) (args : List.Vector (Term ctx) arity) (i : Fin arity) :
 Computes p (.composition .succ (fun _ => .projection i)) args (.succ (args.get i)) := by
 intro tag ht
 obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag .succ (fun _ => .projection i) ht args (args.get i)
  (projection p args i _ (Equations.argumentChild p tag .succ (fun _ => .projection i) ht 0))
 obtain ⟨hs⟩ := Support.intoRegistry p .succ (tag+1)
  (Equations.functionChild p tag .succ (fun _ => .projection i) ht) _
  (NamedArithmeticGraph.Equations.successor (tag+1) ctx (args.get i ::ᵥ nil))
 exact ⟨Logic.trans _ _ _ he hs⟩

theorem counterCall {n m ctx : Nat} (p : Program n) (q : Program (m+1)) (tag : Nat)
 (hq : (nodes p)[tag]? = some ⟨m+1,q⟩) (counter previous : Term ctx) (params : List.Vector (Term ctx) m) :
 Computes p (.composition q (atCounter m)) (counter ::ᵥ previous ::ᵥ params) (familyCall tag counter params) := by
 apply composition p _ q tag hq (atCounter m) (counter ::ᵥ params)
 intro i
 cases i using Fin.cases with
 | zero => exact projection p _ 0
 | succ i => simpa only [atCounter,Fin.cases_succ,List.Vector.get_cons_succ] using
   projection p (counter ::ᵥ previous ::ᵥ params) i.succ.succ

theorem successorCall {n m ctx : Nat} (p : Program n) (q : Program (m+1)) (tag : Nat)
 (hq : (nodes p)[tag]? = some ⟨m+1,q⟩) (counter previous : Term ctx) (params : List.Vector (Term ctx) m) :
 Computes p (.composition q (atSuccessor m)) (counter ::ᵥ previous ::ᵥ params) (familyCall tag (.succ counter) params) := by
 apply composition p _ q tag hq (atSuccessor m) (.succ counter ::ᵥ params)
 intro i
 cases i using Fin.cases with
 | zero => exact successorProjection p _ 0
 | succ i => simpa only [atSuccessor,Fin.cases_succ,List.Vector.get_cons_succ] using
   projection p (counter ::ᵥ previous ::ᵥ params) i.succ.succ

theorem joinCall {n m ctx : Nat} (p : Program n) (formula step : Program (m+1)) (ftag stag mtag : Nat)
 (hf : (nodes p)[ftag]? = some ⟨m+1,formula⟩) (hs : (nodes p)[stag]? = some ⟨m+1,step⟩)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (counter previous : Term ctx) (params : List.Vector (Term ctx) m) :
 Computes p (join formula step) (counter ::ᵥ previous ::ᵥ params)
  (LiteralMPRun.certificate mtag .zero (familyCall ftag (.succ counter) params) (familyCall stag counter params) previous) := by
 apply composition p _ LiteralRawMP.constructor mtag hm _
  (.zero ::ᵥ familyCall ftag (.succ counter) params ::ᵥ familyCall stag counter params ::ᵥ previous ::ᵥ nil)
 intro i
 cases i using Fin.cases with
 | zero => exact constantValue p _ 0
 | succ i => cases i using Fin.cases with
   | zero => exact successorCall p formula ftag hf counter previous params
   | succ i => cases i using Fin.cases with
     | zero => exact counterCall p step stag hs counter previous params
     | succ i => cases i using Fin.cases with
       | zero => exact projection p _ 1
       | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.GraphSupport
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.GraphSupport
