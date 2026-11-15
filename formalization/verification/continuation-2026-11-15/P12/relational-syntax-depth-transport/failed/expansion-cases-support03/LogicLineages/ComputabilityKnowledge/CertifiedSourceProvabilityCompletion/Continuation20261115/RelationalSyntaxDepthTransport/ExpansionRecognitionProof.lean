module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionPairProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionCasesSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRecognitionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof ConstructorStepTargets ExpansionCasesTargets

/-- Recognize an arbitrary raw successful constructor after internal decoded
kind/token equalities; the raw task is reconstructed, never assumed canonical. -/
theorem constructorCaseAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (etag ptag ctag l r : Nat)
 (he : (nodes p)[etag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (task tok added : Term ctx) (ctor : Constructor)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxStep.expandCall etag task tok) (.succ added)))
 (hk : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (call l (task ::ᵥ nil)) (Term.numeral (kind ctor))))
 (ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal tok (Term.numeral (token ctor)))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (constructorCase ptag ctag l r task tok added ctor)) := by
 let bound := call r (task ::ᵥ nil)
 obtain ⟨heta⟩ := ExpansionPairProof.pairEta p ptag l r hp hl hr task
 have hpairs := callCongruence ptag (call l (task ::ᵥ nil) ::ᵥ bound ::ᵥ nil)
  (Term.numeral (kind ctor) ::ᵥ bound ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact hk
   | succ i => cases i using Fin.cases with
     | zero => exact .base (.logical (.reflexive bound))
     | succ i => exact Fin.elim0 i)
 have htask := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ heta)) hpairs
 have hexpand := callCongruence etag (task ::ᵥ tok ::ᵥ nil)
  (LiteralSyntaxStep.taskCall ptag (kind ctor) bound ::ᵥ Term.numeral (token ctor) ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact htask
   | succ i => cases i using Fin.cases with
     | zero => exact ht
     | succ i => exact Fin.elim0 i)
 obtain ⟨hrow⟩ := ConstructorExpansionProof.constructorAt p G ptag ctag hp hc bound ctor etag he
 have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hs) (localTrans _ _ _ hexpand hrow)
 have hadded := Hilbert.Local.mp (.base (.arithmetic (.succInjective _ _))) hsucc
 exact ⟨.mp (.mp (.base (.logical (.andIntro _ _))) hk)
  (.mp (.mp (.base (.logical (.andIntro _ _))) ht) hadded)⟩

noncomputable def injectConstructor {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (ptag ctag dtag l r : Nat) (task tok added : Term ctx) (ctor : Constructor)
 (xs : List Constructor) (hm : ctor ∈ xs)
 (h : Hilbert.Local T ctx G (constructorCase ptag ctag l r task tok added ctor)) :
 Hilbert.Local T ctx G (xs.foldr (fun c rest => .disj (constructorCase ptag ctag l r task tok added c) rest)
  (indexCase dtag l r task tok added)) := by
 induction xs with
 | nil => simp at hm
 | cons c xs ih =>
  rcases List.mem_cons.mp hm with he | ht
  · subst c
    exact .mp (.base (.logical (.orIntroLeft _ _))) h
  · exact .mp (.base (.logical (.orIntroRight _ _))) (ih ht)
noncomputable def injectIndex {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 (ptag ctag dtag l r : Nat) (task tok added : Term ctx) (xs : List Constructor)
 (h : Hilbert.Local T ctx G (indexCase dtag l r task tok added)) :
 Hilbert.Local T ctx G (xs.foldr (fun c rest => .disj (constructorCase ptag ctag l r task tok added c) rest)
  (indexCase dtag l r task tok added)) := by
 induction xs with
 | nil => exact h
 | cons c xs ih => exact .mp (.base (.logical (.orIntroRight _ _))) ih
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRecognitionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ExpansionRecognitionProof
