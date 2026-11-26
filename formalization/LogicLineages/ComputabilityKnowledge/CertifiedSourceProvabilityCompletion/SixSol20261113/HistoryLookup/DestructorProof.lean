module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DestructorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

noncomputable def unaryCallCongruence {T : Sentence → Prop} {ctx : Nat} tag (s t : Term ctx)
    (h : Derivation T (.equal s t)) : Derivation T (.equal (call tag (s ::ᵥ nil)) (call tag (t ::ᵥ nil))) := by
  have d := Logic.unary (call tag (.var 0 ::ᵥ nil)) s t h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,Fin.cases_zero] using d

theorem decoderCrossPair {n ctx : Nat} (p : Program n) dtag ptag right
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder right⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call dtag (call ptag (a ::ᵥ b ::ᵥ nil) ::ᵥ nil)) (HistoryDecoder.StepNormalProof.chosen right a b))) := by
  have hown := HistoryDecoder.InstalledProof.pairInstalled p dtag right hd
  obtain ⟨hc⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p ptag (HistoryDecoder.pairTag right dtag) hp hown a b
  obtain ⟨hi⟩ := HistoryDecoder.InverseProof.inverse p dtag right hd a b
  exact ⟨Logic.trans _ _ _ (unaryCallCongruence dtag _ _ hc) hi⟩

theorem pairZero {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call (ctx := ctx) tag (.zero ::ᵥ .zero ::ᵥ nil)) .zero)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨ho⟩ := HistoryOrder.PairProof.pairUpperOrder n p tag ht ctx .zero .zero
  have h := Derivation.mp ho (HistoryCancellation.OrderSupportProof.weakReflexive (T := T) (.zero : Term ctx))
  have he : Derivation T (.equal (.add (.add (.mul (.zero : Term ctx) .zero) .zero) .zero) .zero) :=
    Logic.trans _ _ _ (.arithmetic (.addZero _))
      (Logic.trans _ _ _ (.arithmetic (.addZero _)) (.arithmetic (.mulZero .zero)))
  exact ⟨Logic.trans _ _ _ h he⟩

theorem decoderZero {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,HistoryDecoder.decoder right⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (ctx := ctx) tag (.zero ::ᵥ nil)) .zero)) := by
  obtain ⟨hp⟩ := pairZero (ctx := ctx) p (HistoryDecoder.pairTag right tag)
    (HistoryDecoder.InstalledProof.pairInstalled p tag right ht)
  obtain ⟨hi⟩ := HistoryDecoder.InverseProof.inverse p tag right ht (.zero : Term ctx) .zero
  have hc := unaryCallCongruence tag _ _ hp
  have h := Logic.trans _ _ _ (Support.equalitySymmetry _ _ hc) hi
  cases right <;> exact ⟨h⟩

def predTag (right : Bool) (tag : Nat) := tag + argumentTag (HistoryDecoder.decoder right) (fun _ : Fin 1 => HistoryCodec.predecessor) 0

theorem destructorEquation {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,.composition (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor)⟩)
    (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (code ::ᵥ nil)) (call (tag+1) (call (predTag right tag) (code ::ᵥ nil) ::ᵥ nil)))) := by
  obtain ⟨h⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag 1 1
    (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor) ht ctx (code ::ᵥ nil)
  exact ⟨h⟩

theorem destructorCons {n ctx : Nat} (p : Program n) tag ctag right
    (ht : (nodes p)[tag]? = some ⟨1,.composition (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor)⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (consCall ctag a b ::ᵥ nil)) (HistoryDecoder.StepNormalProof.chosen right a b))) := by
  let cp := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  let value := call cp (a ::ᵥ b ::ᵥ nil)
  have hpair := SixSol20261112.Fuel.Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  have hd := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor) ht
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor) ht 0
  obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx a b
  obtain ⟨hpred⟩ := HistoryDifference.EquationsProof.predecessorSuccessor n p (predTag right tag) hp ctx value
  have hpc := Logic.trans _ _ _ (unaryCallCongruence (predTag right tag) _ _ hcons) hpred
  obtain ⟨he⟩ := destructorEquation p tag right ht (consCall ctag a b)
  obtain ⟨hinv⟩ := decoderCrossPair p (tag+1) cp right hd hpair a b
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (unaryCallCongruence (tag+1) _ _ hpc) hinv)⟩

theorem destructorZero {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,.composition (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor)⟩) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (ctx := ctx) tag (.zero ::ᵥ nil)) .zero)) := by
  have hd := SixSol20261112.Fuel.Equations.functionChild p tag (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor) ht
  have hp := SixSol20261112.Fuel.Equations.argumentChild p tag (HistoryDecoder.decoder right) (fun _ => HistoryCodec.predecessor) ht 0
  obtain ⟨he⟩ := destructorEquation p tag right ht (.zero : Term ctx)
  obtain ⟨hz⟩ := HistoryDifference.EquationsProof.predecessorZero n p (predTag right tag) hp ctx
  obtain ⟨hdz⟩ := decoderZero (ctx := ctx) p (tag+1) right hd
  exact ⟨Logic.trans _ _ _ he (Logic.trans _ _ _ (unaryCallCongruence (tag+1) _ _ hz) hdz)⟩

theorem internalHeadCons : Targets.InternalHeadCons := by
  intro n p htag ctag hh hc ctx a b
  exact destructorCons p htag ctag false hh hc a b

theorem internalTailCons : Targets.InternalTailCons := by
  intro n p ttag ctag ht hc ctx a b
  exact destructorCons p ttag ctag true ht hc a b

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.DestructorProof
