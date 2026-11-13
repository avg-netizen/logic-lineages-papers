module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.NativeProof
open GorbowPRProgram List.Vector HistoryCodec.NativeProof

def coordinate (right : Bool) (a b : Nat) : Nat := if right then b else a

def scanInner (right : Bool) (a code seed : Nat) : Nat → Nat
  | 0 => seed
  | b+1 => if Nat.pair a b = code then coordinate right a b else scanInner right a code seed b

def scanOuter (right : Bool) (code : Nat) : Nat → Nat
  | 0 => 0
  | a+1 => scanInner right a code (scanOuter right code a) (code+1)

theorem evaluateChoose {n : Nat} (test yes no : Program n) (v : List.Vector Nat n) :
    evaluate (choose test yes no) v =
      if evaluate test v = 0 then evaluate yes v else evaluate no v := by
  change evaluate HistoryCodec.select
    (evaluate test v ::ᵥ evaluate yes v ::ᵥ evaluate no v ::ᵥ nil) = _
  exact evaluateSelect _ _ _

theorem evaluateStep (right : Bool) (b previous a code seed : Nat) :
    evaluate (innerStep right) (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) =
      if Nat.pair a b = code then coordinate right a b else previous := by
  change evaluate HistoryCodec.select
    (evaluate forward (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) ::ᵥ
      evaluate (choose backward (.projection (if right then 0 else 2)) (.projection 1))
        (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) ::ᵥ previous ::ᵥ nil) = _
  rw [evaluateSelect,evaluateChoose]
  have hf : evaluate forward (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) = code - Nat.pair a b := by
    change evaluate HistoryCodec.difference (evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) ::ᵥ code ::ᵥ nil) = _
    rw [evaluateDifference,nativePair]
    rfl
  have hb : evaluate backward (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) = Nat.pair a b - code := by
    change evaluate HistoryCodec.difference (code ::ᵥ evaluate HistoryCodec.pair (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) = _
    rw [evaluateDifference,nativePair]
    rfl
  rw [hf,hb]
  cases right <;> simp only [coordinate,Bool.false_eq_true,↓reduceIte,evaluate,
    List.Vector.get_cons_zero,List.Vector.get_cons_succ] <;> split_ifs <;> omega

theorem evaluateInner (right : Bool) (count a code seed : Nat) :
    evaluate (inner right) (count ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) = scanInner right a code seed count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change evaluate (innerStep right)
        (count ::ᵥ evaluate (inner right) (count ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) = _
      rw [evaluateStep,ih]
      rfl

theorem evaluateOuter (right : Bool) (count code : Nat) :
    evaluate (outer right) (count ::ᵥ code ::ᵥ nil) = scanOuter right code count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change evaluate (inner right)
        ((code+1) ::ᵥ count ::ᵥ code ::ᵥ evaluate (outer right) (count ::ᵥ code ::ᵥ nil) ::ᵥ nil) = _
      rw [evaluateInner,ih]
      rfl

theorem innerPreserve (right : Bool) (u v a count : Nat) :
    scanInner right a (Nat.pair u v) (coordinate right u v) count = coordinate right u v := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [scanInner]
      split_ifs with h
      · obtain ⟨rfl,rfl⟩ := Nat.pair_eq_pair.mp h
        rfl
      · exact ih

theorem innerFind (right : Bool) (u v count seed : Nat) (h : v < count) :
    scanInner right u (Nat.pair u v) seed count = coordinate right u v := by
  induction count with
  | zero => omega
  | succ count ih =>
      simp only [scanInner]
      split_ifs with he
      · obtain ⟨_,hc⟩ := Nat.pair_eq_pair.mp he
        subst count
        rfl
      · apply ih
        have hn : count ≠ v := by intro e; subst count; exact he rfl
        omega

theorem outerFind (right : Bool) (u v count : Nat) (h : u < count) :
    scanOuter right (Nat.pair u v) count = coordinate right u v := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [scanOuter]
      by_cases he : count = u
      · subst count
        exact innerFind right u v _ _ (Nat.lt_succ_of_le (Nat.right_le_pair u v))
      · rw [ih (by omega)]
        exact innerPreserve right u v count _

theorem evaluateDecoder (right : Bool) (code : Nat) :
    evaluate (decoder right) (code ::ᵥ nil) = coordinate right (Nat.unpair code).1 (Nat.unpair code).2 := by
  change evaluate (outer right) ((code+1) ::ᵥ code ::ᵥ nil) = _
  rw [evaluateOuter]
  have h := outerFind right (Nat.unpair code).1 (Nat.unpair code).2 (code+1)
    (Nat.lt_succ_of_le (Nat.unpair_left_le code))
  simpa only [Nat.pair_unpair] using h

theorem nativeLeft : Targets.NativeLeft := by
  intro v
  have hv : v = v.head ::ᵥ nil := by
    simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
  rw [hv]
  exact evaluateDecoder false _

theorem nativeRight : Targets.NativeRight := by
  intro v
  have hv : v = v.head ::ᵥ nil := by
    simpa only [List.Vector.singleton_tail] using (List.Vector.cons_head_tail v).symm
  rw [hv]
  exact evaluateDecoder true _

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.NativeProof
