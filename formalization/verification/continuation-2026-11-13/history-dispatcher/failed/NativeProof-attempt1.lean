module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix HistoryRuleSuffix.NativeProof
open GorbowProofChecker (Line History context conclusion rule payload)

def inputs (index fuel : Nat) (h : History) (l : Line) : List.Vector Nat 4 :=
  index ::ᵥ fuel ::ᵥ Encodable.encode h ::ᵥ Encodable.encode l ::ᵥ nil

theorem encodeProd {α β : Type} [Encodable α] [Encodable β] (a : α) (b : β) :
    Encodable.encode (a,b) = Nat.pair (Encodable.encode a) (Encodable.encode b) := rfl
theorem encodeNat (n : Nat) : Encodable.encode n = n := rfl

theorem leftEval (q : Program 4) (v : List.Vector Nat 4) :
    evaluate (left q) v = (Nat.unpair (evaluate q v)).1 := by
  rw [left,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]; rfl
theorem rightEval (q : Program 4) (v : List.Vector Nat 4) :
    evaluate (right q) v = (Nat.unpair (evaluate q v)).2 := by
  rw [right,oneEval,HistoryDecoder.NativeProof.evaluateDecoder]; rfl

theorem contextCodeEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate contextCode (inputs index fuel h l) = context l := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem rawCodeEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate rawCode (inputs index fuel h l) = Encodable.encode (conclusion l) := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem ruleCodeEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate ruleCode (inputs index fuel h l) = rule l := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem payloadTagEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate payloadTag (inputs index fuel h l) = (payload l).1 := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem payloadArgsEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate payloadArgs (inputs index fuel h l) = Encodable.encode (payload l).2.1 := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem ref1Eval (index fuel : Nat) (h : History) (l : Line) :
    evaluate ref1 (inputs index fuel h l) = (payload l).2.2.1 := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem ref2Eval (index fuel : Nat) (h : History) (l : Line) :
    evaluate ref2 (inputs index fuel h l) = (payload l).2.2.2 := by
  rcases l with ⟨n,raw,r,pt,pa,r1,r2⟩
  simp only [contextCode,rawCode,ruleCode,payloadCode,payloadTag,payloadArgs,ref1,ref2,
    leftEval,rightEval,lineCode,projectionEval,inputs,get4_3,encodeProd,encodeNat,Nat.unpair_pair]
  rfl

theorem zeroTestEval (q : Program 4) (v : List.Vector Nat 4) :
    evaluate (zeroTest q) v = if evaluate q v=0 then 1 else 0 := by
  rw [zeroTest,twoEval,constantEval,equalEval]

theorem commonGuardEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate commonGuard (inputs index fuel h l) =
      if (payload l).1=0 ∧ (payload l).2.1=[] then 1 else 0 := by
  simp only [commonGuard,conjunctionEval,zeroTestEval,payloadTagEval,payloadArgsEval]
  have he : (Encodable.encode (payload l).2.1=0) ↔ (payload l).2.1=[] := by
    change (Encodable.encode (payload l).2.1=Encodable.encode ([] : List (List Nat))) ↔ _
    exact Encodable.encode_inj
  rw [he]
  by_cases h1 : (payload l).1=0 <;> by_cases h2 : (payload l).2.1=[] <;> simp [h1,h2]

theorem generalizeGuardEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate generalizeGuard (inputs index fuel h l) =
      if (payload l).1=0 ∧ (payload l).2.1=[] ∧ (payload l).2.2.2=0 then 1 else 0 := by
  simp only [generalizeGuard,conjunctionEval,commonGuardEval,zeroTestEval,ref2Eval]
  by_cases h1 : (payload l).1=0 <;> by_cases h2 : (payload l).2.1=[] <;>
    by_cases h3 : (payload l).2.2.2=0 <;> simp [h1,h2,h3]

theorem mpCallEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate (.composition mpCheck mpArguments) (inputs index fuel h l) =
      truth (GorbowProofChecker.ruleCheck h (GorbowProofChecker.mpLine
        (context l) (conclusion l) (payload l).2.2.1 (payload l).2.2.2)) := by
  change evaluate mpCheck (evaluate (.projection 2) (inputs index fuel h l) ::ᵥ
    evaluate contextCode (inputs index fuel h l) ::ᵥ evaluate rawCode (inputs index fuel h l) ::ᵥ
    evaluate ref1 (inputs index fuel h l) ::ᵥ evaluate ref2 (inputs index fuel h l) ::ᵥ nil) = _
  rw [projectionEval,contextCodeEval,rawCodeEval,ref1Eval,ref2Eval]
  exact HistoryRuleSuffix.NativeProof.nativeMP h (context l) (conclusion l) _ _

theorem generalizeCallEval (index fuel : Nat) (h : History) (l : Line) :
    evaluate (.composition generalizeCheck generalizeArguments) (inputs index fuel h l) =
      truth (GorbowProofChecker.ruleCheck h (GorbowProofChecker.generalizeLine
        (context l) (conclusion l) (payload l).2.2.1)) := by
  change evaluate generalizeCheck (evaluate (.projection 2) (inputs index fuel h l) ::ᵥ
    evaluate contextCode (inputs index fuel h l) ::ᵥ evaluate rawCode (inputs index fuel h l) ::ᵥ
    evaluate ref1 (inputs index fuel h l) ::ᵥ nil) = _
  rw [projectionEval,contextCodeEval,rawCodeEval,ref1Eval]
  exact HistoryRuleSuffix.NativeProof.nativeGeneralize h (context l) (conclusion l) _

theorem ruleSelectEval (r : Nat) (yes no : Program 4) (index fuel : Nat) (h : History) (l : Line) :
    evaluate (ruleSelect r yes no) (inputs index fuel h l) =
      if rule l=r then evaluate yes (inputs index fuel h l) else evaluate no (inputs index fuel h l) := by
  simp only [ruleSelect,chooseEval,twoEval,ruleCodeEval,constantEval,equalEval]
  by_cases hr : rule l=r <;> simp [hr]

theorem decodedEncode (l : Line) : decodedLine (Encodable.encode l) = l := by
  simp only [decodedLine,Encodable.encodek,Option.getD_some]

theorem unaryLeafEval (q : Program 1) (index fuel : Nat) (h : History) (l : Line) :
    evaluate (applyOne q lineCode) (inputs index fuel h l) =
      evaluate q (Encodable.encode l ::ᵥ nil) := rfl

theorem axiomLeafEval (q : Program 3) (index fuel : Nat) (h : History) (l : Line) :
    evaluate (.composition q axiomArguments) (inputs index fuel h l) =
      evaluate q (index ::ᵥ fuel ::ᵥ Encodable.encode l ::ᵥ nil) := rfl

theorem nativeLineDispatcher : Targets.NativeLineDispatcher := by
  intro valid logical arithmetic axiomProgram hleaves index fuel h l
  obtain ⟨hv,hl,ha,hax⟩ := hleaves
  have ev := hv (Encodable.encode l ::ᵥ nil)
  have el := hl (Encodable.encode l ::ᵥ nil)
  have ea := ha (Encodable.encode l ::ᵥ nil)
  have ex := hax (index ::ᵥ fuel ::ᵥ Encodable.encode l ::ᵥ nil)
  simp only [validFunction,logicalFunction,arithmeticFunction,axiomFunction,
    List.Vector.head_cons,List.Vector.tail_cons,decodedEncode] at ev el ea ex
  change evaluate (lineDispatcher valid logical arithmetic axiomProgram) (inputs index fuel h l) = _
  simp only [lineDispatcher,conjunctionEval,ruleDispatcher,ruleSelectEval,unaryLeafEval,
    axiomLeafEval,ev,el,ea,ex,mpBranch,generalizeBranch,commonGuardEval,generalizeGuardEval,
    mpCallEval,generalizeCallEval,constantEval]
  by_cases h0 : rule l=0 <;> by_cases h1 : rule l=1 <;>
    by_cases h2 : rule l=2 <;> by_cases h3 : rule l=3 <;> by_cases h4 : rule l=4 <;>
    simp_all [truth,GorbowTheoryChecker.lineCheck,GorbowTheoryChecker.ruleCheck,
      GorbowProofChecker.ruleCheck,withRule,GorbowProofChecker.mpLine,GorbowProofChecker.generalizeLine,
      GorbowProofChecker.context,GorbowProofChecker.conclusion,GorbowProofChecker.payload,GorbowProofChecker.rule]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.NativeProof
