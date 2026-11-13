module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.TrichotomyProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryCancellation.ShellProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.DoubleProof
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryBounds HistoryBounds.SupportProof
open HistoryCancellation

theorem strictDouble (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
 Nonempty (Derivation T (.imp (strictBound a b) (strictBound (.add a a) (.add b b)))) := by
 let H := strictBound a b
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 obtain ⟨h1⟩ := MonotonicityProof.strictAddLeft T a b a
 obtain ⟨h2⟩ := MonotonicityProof.weakAddLeft T a b b
 obtain ⟨hw⟩ := ShellProof.strictToWeak T a b
 obtain ⟨ht⟩ := TransitivityProof.strictWeakTrans T (.add a a) (.add a b) (.add b b)
 have w := Hilbert.Local.mp (.base h2) (.mp (.base hw) hh)
 have w' : Hilbert.Local T ctx [H] (weakBound (.add a b) (.add b b)) :=
  .mp (.mp (.base (MonotonicityProof.weakChildTransport (.add a b) (.add b a) (.add b b)))
    (.base (addComm a b))) w
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.mp (.base ht) (.mp (.base h1) hh)) w'))⟩

theorem strictReject (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
 Nonempty (Derivation T (.imp (strictBound a b)
  (.imp (.equal (.add a a) (.add b b)) (.equal a b)))) := by
 let H := strictBound a b
 let E := Formula.equal (.add a a) (.add b b)
 have hh : Hilbert.Local T ctx [E,H] H := .hypothesis (by simp)
 have he : Hilbert.Local T ctx [E,H] E := .hypothesis List.mem_cons_self
 obtain ⟨hd⟩ := strictDouble T a b
 obtain ⟨hi⟩ := OrderSupportProof.strictIrreflexive T (.add a a)
 have hs : Hilbert.Local T ctx [E,H] (strictBound (.add a a) (.add a a)) :=
  .mp (.mp (.base (HistoryBounds.PairProof.strictTransport (.add a a) (.add a a) (.add b b))) he)
   (.mp (.base hd) hh)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
  (Hilbert.Local.explosion (.equal a b) hs (.base hi))))⟩

theorem injective (T : Sentence → Prop) {ctx : Nat} (a b : Term ctx) :
 Nonempty (Derivation T (.imp (.equal (.add a a) (.add b b)) (.equal a b))) := by
 let E := Formula.equal (.add a a) (.add b b)
 let Q := Formula.imp E (.equal a b)
 obtain ⟨hl⟩ := strictReject T a b
 obtain ⟨hr⟩ := strictReject T b a
 have hh : Hilbert.Local T ctx [E,strictBound b a] E := .hypothesis List.mem_cons_self
 have hs : Hilbert.Local T ctx [E,strictBound b a] (strictBound b a) := .hypothesis (by simp)
 have hb := Hilbert.Local.mp (.mp (.base hr) hs) (HistoryOrder.StepProof.localSym _ _ hh)
 have hrev : Derivation T (.imp (strictBound b a) Q) :=
  Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge
   (HistoryOrder.StepProof.localSym _ _ hb)))
 have heq : Derivation T (.imp (.equal a b) Q) := .logical (.k _ _)
 obtain ⟨htri⟩ := TrichotomyProof.trichotomy T a b
 have hrest : Derivation T (.imp (.disj (.equal a b) (strictBound b a)) Q) :=
  .mp (.mp (.logical (.orElim _ _ _)) heq) hrev
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hrest) htri⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.DoubleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.DoubleProof
