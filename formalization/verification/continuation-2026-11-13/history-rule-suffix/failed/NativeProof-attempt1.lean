module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.NativeProof
open GorbowPRProgram List.Vector

theorem constantEval (n k : Nat) (v : Vector Nat n) : evaluate (constant n k) v = k := by
  induction k with
  | zero => rfl
  | succ k ih => change (evaluate (constant n k) v).succ = k.succ; rw [ih]

theorem oneEval {n : Nat} (f : Program 1) (a : Program n) (v : Vector Nat n) :
    evaluate (applyOne f a) v = evaluate f (evaluate a v ::ᵥ nil) := rfl
theorem twoEval {n : Nat} (f : Program 2) (a b : Program n) (v : Vector Nat n) :
    evaluate (applyTwo f a b) v = evaluate f (evaluate a v ::ᵥ evaluate b v ::ᵥ nil) := rfl
theorem chooseEval {n : Nat} (t a b : Program n) (v : Vector Nat n) :
    evaluate (choose t a b) v = if evaluate t v=0 then evaluate a v else evaluate b v := by
  change evaluate HistoryCodec.select (evaluate t v ::ᵥ evaluate a v ::ᵥ evaluate b v ::ᵥ nil) = _
  exact HistoryCodec.NativeProof.evaluateSelect _ _ _

theorem equalEval (a b : Nat) : evaluate equalCode (a ::ᵥ b ::ᵥ nil) = if a=b then 1 else 0 := by
  simp only [equalCode,chooseEval,twoEval,constantEval]
  change (if b-a=0 then (if a-b=0 then 1 else 0) else 0) = _
  by_cases h : a=b
  · subst b; simp
  · have hh : ¬ (b-a=0 ∧ a-b=0) := by omega
    by_cases hba : b-a=0 <;> simp_all

theorem conjunctionEval {n : Nat} (a b : Program n) (v : Vector Nat n) :
    evaluate (conjunction a b) v = if evaluate a v=0 then 0 else evaluate b v := by
  simp only [conjunction,chooseEval,constantEval]

theorem partEval {n : Nat} (right : Bool) (a : Program n) (v : Vector Nat n) :
    evaluate (entryPart right a) v =
      if right then (Nat.unpair (evaluate a v).pred).2 else (Nat.unpair (evaluate a v).pred).1 := by
  rw [entryPart,oneEval,oneEval,HistoryCodec.NativeProof.evaluatePredecessor,
    HistoryDecoder.NativeProof.evaluateDecoder]
  cases right <;> rfl

theorem appendList {α : Type} [Encodable α] (left right : List α) :
    evaluate HistoryAppend.append (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) =
      Encodable.encode (left++right) := by
  rw [HistoryAppend.NativeProof.appendEval]
  induction left with
  | nil => rfl
  | cons a left ih =>
      rw [HistoryLookup.NativeProof.encodeCons,HistoryAppend.NativeProof.resultCons,ih]
      rfl

theorem mpBodyEval (n : Nat) (raw : List Nat) (a b : Option GorbowProofChecker.Entry) :
    evaluate mpBody (n ::ᵥ Encodable.encode raw ::ᵥ Encodable.encode a ::ᵥ Encodable.encode b ::ᵥ nil) =
      match a,b with
      | some a,some b => if a.1=n ∧ b.1=n ∧ a.2=GorbowCodeConstructors.binary 7 b.2 raw then 1 else 0
      | _,_ => 0 := by
  cases a with
  | none => simp only [mpBody,chooseEval]; rfl
  | some a => cases b with
    | none => simp only [mpBody,chooseEval]; rfl
    | some b =>
      rcases a with ⟨an,ar⟩
      rcases b with ⟨bn,br⟩
      simp only [mpBody,chooseEval,conjunctionEval,twoEval,partEval,constantEval]
      change (if (Nat.pair an (Encodable.encode ar)).succ=0 then 0 else
        if (Nat.pair bn (Encodable.encode br)).succ=0 then 0 else
        if evaluate equalCode (an ::ᵥ n ::ᵥ nil)=0 then 0 else
        if evaluate equalCode (bn ::ᵥ n ::ᵥ nil)=0 then 0 else
        evaluate equalCode (Encodable.encode ar ::ᵥ
          evaluate HistoryCodec.cons (7 ::ᵥ evaluate HistoryAppend.append
            (Encodable.encode br ::ᵥ Encodable.encode raw ::ᵥ nil) ::ᵥ nil) ::ᵥ nil)) = _
      rw [appendList,HistoryCodec.NativeProof.nativeConsAllVectors]
      simp only [Nat.succ_ne_zero,if_false,equalEval]
      have hc : (Nat.pair 7 (Encodable.encode (br++raw))).succ =
          Encodable.encode (GorbowCodeConstructors.binary 7 br raw) := rfl
      rw [hc]
      simp only [Encodable.encode_inj]
      by_cases h1 : an=n <;> by_cases h2 : bn=n <;>
        by_cases h3 : ar=GorbowCodeConstructors.binary 7 br raw <;> simp [h1,h2,h3]

theorem generalizeBodyEval (n : Nat) (raw : List Nat) (a : Option GorbowProofChecker.Entry) :
    evaluate generalizeBody (n ::ᵥ Encodable.encode raw ::ᵥ Encodable.encode a ::ᵥ nil) =
      match a with
      | some a => if a.1=n+1 ∧ raw=GorbowCodeConstructors.unary 10 a.2 then 1 else 0
      | none => 0 := by
  cases a with
  | none => simp only [generalizeBody,chooseEval]; rfl
  | some a =>
      rcases a with ⟨an,ar⟩
      simp only [generalizeBody,chooseEval,conjunctionEval,twoEval,oneEval,partEval,constantEval]
      change (if (Nat.pair an (Encodable.encode ar)).succ=0 then 0 else
        if evaluate equalCode (an ::ᵥ n.succ ::ᵥ nil)=0 then 0 else
        evaluate equalCode (Encodable.encode raw ::ᵥ
          evaluate HistoryCodec.cons (10 ::ᵥ Encodable.encode ar ::ᵥ nil) ::ᵥ nil)) = _
      rw [HistoryCodec.NativeProof.nativeConsAllVectors]
      have hc : (Nat.pair 10 (Encodable.encode ar)).succ =
          Encodable.encode (GorbowCodeConstructors.unary 10 ar) := rfl
      rw [hc]
      simp only [Nat.succ_ne_zero,if_false,equalEval,Encodable.encode_inj]
      by_cases h1 : an=n+1 <;> by_cases h2 : raw=GorbowCodeConstructors.unary 10 ar <;> simp [h1,h2]

theorem nativeMP : Targets.NativeMP := by
  intro h n raw r1 r2
  change evaluate mpBody (n ::ᵥ Encodable.encode raw ::ᵥ
    evaluate HistoryLookup.lookup (r1 ::ᵥ Encodable.encode h ::ᵥ nil) ::ᵥ
    evaluate HistoryLookup.lookup (r2 ::ᵥ Encodable.encode h ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryLookup.NativeProof.nativeHistoryLookup,HistoryLookup.NativeProof.nativeHistoryLookup,mpBodyEval]
  cases h[r1]? <;> cases h[r2]? <;>
    simp [GorbowProofChecker.ruleCheck,GorbowProofChecker.mpLine,GorbowProofChecker.context,
      GorbowProofChecker.conclusion,GorbowProofChecker.payload,GorbowProofChecker.rule]

theorem nativeGeneralize : Targets.NativeGeneralize := by
  intro h n raw r
  change evaluate generalizeBody (n ::ᵥ Encodable.encode raw ::ᵥ
    evaluate HistoryLookup.lookup (r ::ᵥ Encodable.encode h ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryLookup.NativeProof.nativeHistoryLookup,generalizeBodyEval]
  cases h[r]? <;>
    simp [GorbowProofChecker.ruleCheck,GorbowProofChecker.generalizeLine,GorbowProofChecker.context,
      GorbowProofChecker.conclusion,GorbowProofChecker.payload,GorbowProofChecker.rule]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.NativeProof
