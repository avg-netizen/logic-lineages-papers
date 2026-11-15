module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorStepTargets ExpansionCasesTargets ExpansionCasesSupportProof
/-- All nineteen original successful runtime expansion arms are exhausted.
The known decoded term kind eliminates twelve formula arms and the index arm
internally, leaving exactly six token continuations. No native token witness. -/
theorem eliminate {n ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (xtag ptag ctag dtag l r : Nat)
 (hx : (nodes p)[xtag]? = some ⟨2,LiteralSyntaxStep.expandCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (hd : (nodes p)[dtag]? = some ⟨2,HistoryCodec.difference⟩)
 (hl : (nodes p)[l]? = some ⟨1,HistoryDecoder.decoder false⟩)
 (hr : (nodes p)[r]? = some ⟨1,HistoryDecoder.decoder true⟩)
 (task tok added : Term ctx) (Q : Formula ctx)
 (hk0 : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (call l (task ::ᵥ nil)) .zero))
 (hex : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (.equal (LiteralSyntaxStep.expandCall xtag task tok) (.succ added)))
 (hterms : ∀ i : Fin 6, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.imp (.equal tok (Term.numeral i.val)) Q))) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G Q) := by
 let T := GorbowPRNumeralCalculation.Theory p
 have hctors : ∀ ctor, Nonempty (Hilbert.Local T ctx G (.imp (constructorCase ptag ctag l r task tok added ctor) Q)) := by
  intro ctor
  let C := constructorCase ptag ctag l r task tok added ctor
  have hcase : Hilbert.Local T ctx (C :: G) C := .hypothesis List.mem_cons_self
  have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hcase
  cases ctor with
  | term i =>
   have hb := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hcase
   have ht := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
   obtain ⟨hi⟩ := hterms i
   exact ⟨(Hilbert.Local.mp (push C hi) ht).discharge⟩
  | formula i =>
   have hbad : Hilbert.Local T ctx (C :: G) (.equal (.succ .zero) .zero) :=
    localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hk) (push C hk0)
   exact ⟨(Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero .zero)))).discharge⟩
 let I := indexCase dtag l r task tok added
 have hi : Hilbert.Local T ctx (I :: G) I := .hypothesis List.mem_cons_self
 have hk := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hi
 have hbad : Hilbert.Local T ctx (I :: G) (.equal (.succ (.succ .zero)) .zero) :=
  localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hk) (push I hk0)
 have hind := (Hilbert.Local.explosion Q hbad (.base (.arithmetic (.succNotZero (.succ .zero))))).discharge
 obtain ⟨hall⟩ := StepTransportCasesProof.foldCases constructors (constructorCase ptag ctag l r task tok added) I Q hctors hind
 obtain ⟨hclass⟩ := ExpansionCasesProof.expansionSuccessCases n p xtag ptag ctag dtag l r hx hp hc hd hl hr ctx task tok added
 exact ⟨Hilbert.Local.mp hall (.mp (.base hclass) hex)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedTermFrame.TermCasesProof
