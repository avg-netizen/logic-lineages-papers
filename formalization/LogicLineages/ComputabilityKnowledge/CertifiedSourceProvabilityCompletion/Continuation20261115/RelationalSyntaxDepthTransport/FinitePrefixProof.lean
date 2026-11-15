module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open SubstitutionProof FinitePrefixTargets

noncomputable def stackLeft {T : Sentence → Prop} {ctx : Nat} len q l r (a b t : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (stackRelation len q l r a t) (stackRelation len q l r b t))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (stackRelation len q l r (.var 0) (liftTerm t)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substStack,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def stackRight {T : Sentence → Prop} {ctx : Nat} len q l r (t a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (stackRelation len q l r t a) (stackRelation len q l r t b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (stackRelation len q l r (liftTerm t) (.var 0)) a b)
 simpa only [GorbowPACore.logicalFormula,GorbowStandardInstances.instantiate,substStack,
  substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using h
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
 len q l r (a b a' b' : Term ctx)
 (ha : Derivation T (.equal a a')) (hb : Derivation T (.equal b b'))
 (hr : Hilbert.Local T ctx G (stackRelation len q l r a' b')) :
 Hilbert.Local T ctx G (stackRelation len q l r a b) := by
 have hl := Hilbert.Local.mp (.mp (.base (stackLeft len q l r a' a b'))
  (.base (Support.equalitySymmetry _ _ ha))) hr
 exact .mp (.mp (.base (stackRight len q l r a b' b))
  (.base (Support.equalitySymmetry _ _ hb))) hl

/-- The only induction here is over explicit finite constructor prefixes.
Each recursive relation is a genuine local internal derivation. -/
theorem finitePrefixAppend : FinitePrefixTargets.InternalFinitePrefixAppend := by
 intro n p len q l r ctag atag hl hq hc ha ctx G xs ys tail newTail hprefix htail
 obtain ⟨ht⟩ := htail
 induction hprefix with
 | nil =>
  obtain ⟨ho⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx tail
  obtain ⟨hn⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p atag ha ctx newTail
  exact ⟨transport len q l r _ _ _ _ ho hn ht⟩
 | @cons x y xs ys hhead hrest ih =>
  obtain ⟨hh⟩ := hhead
  obtain ⟨hr⟩ := ih
  obtain ⟨hcons⟩ := ConsProof.consRelated p len q l r ctag hl hq hc
   x (HistoryAppend.appendCall atag (prefixTerm ctag xs) tail)
   y (HistoryAppend.appendCall atag (prefixTerm ctag ys) newTail)
  have hb := Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hh) hr
  have hout := Hilbert.Local.mp (.base hcons) hb
  obtain ⟨ho⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx x (prefixTerm ctag xs) tail
  obtain ⟨hn⟩ := HistoryAppend.ConsProof.internalAppendCons n p atag ctag ha hc ctx y (prefixTerm ctag ys) newTail
  exact ⟨transport len q l r _ _ _ _ ho hn hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.FinitePrefixProof
