import LogicLineages.PersistentMarking.NameBridge
namespace LogicLineages.PersistentMarking.AlphaSizeProof
open NameBridge

mutual
 def nodes : Term → Nat
   | .var _ _ => 1
   | .lam _ _ body => 1 + nodes body
   | .head _ base => 1 + argsNodes base
   | .marked _ _ base extras => 1 + argsNodes base + argsNodes extras
 def argsNodes : List Term → Nat
   | [] => 0
   | q::qs => 1 + nodes q + argsNodes qs
end

mutual
 theorem renameNodes (old new : Name) (q : Term) : nodes (renameFree old new q) = nodes q := by
  cases q with
  | var σ x => by_cases h : (σ,x) = old <;> simp [renameFree, h, nodes]
  | lam σ x body =>
    by_cases h : (σ,x) = old <;> simp [renameFree, h, nodes, renameNodes old new body]
  | head f base => simp only [renameFree, nodes, renameArgsNodes old new base]
  | marked f τ base extras => simp only [renameFree, nodes, renameArgsNodes old new base, renameArgsNodes old new extras]
 termination_by sizeOf q
 theorem renameArgsNodes (old new : Name) (qs : List Term) : argsNodes (renameFreeArgs old new qs) = argsNodes qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [renameFreeArgs, argsNodes, renameNodes old new q, renameArgsNodes old new qs]
 termination_by sizeOf qs
end

mutual
 def maxNamed : Term → Nat
   | .var _ x => x
   | .lam _ x body => max x (maxNamed body)
   | .head _ base => maxArgs base
   | .marked _ _ base extras => max (maxArgs base) (maxArgs extras)
 def maxArgs : List Term → Nat
   | [] => 0
   | q::qs => max (maxNamed q) (maxArgs qs)
end

mutual
 theorem aboveFresh (σ : Ty) (z : Nat) (q : Term) (h : maxNamed q < z) : nameOccurs (σ,z) q = false := by
  cases q with
  | var δ x =>
    have hn : (σ,z) ≠ (δ,x) := by
      intro he
      have hx := congrArg Prod.snd he
      simp only [maxNamed] at h
      simp only at hx
      omega
    simp [nameOccurs, hn]
  | lam δ x body =>
    have hx : x < z := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hb : maxNamed body < z := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    have hn : (σ,z) ≠ (δ,x) := by
      intro he
      have hh := congrArg Prod.snd he
      simp only at hh
      omega
    simp [nameOccurs, hn, aboveFresh σ z body hb]
  | head f base => exact aboveFreshArgs σ z base h
  | marked f τ base extras =>
    have hb : maxArgs base < z := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have he : maxArgs extras < z := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    simp only [nameOccurs, aboveFreshArgs σ z base hb, aboveFreshArgs σ z extras he, Bool.false_or]
 termination_by sizeOf q
 theorem aboveFreshArgs (σ : Ty) (z : Nat) (qs : List Term) (h : maxArgs qs < z) : namesOccur (σ,z) qs = false := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    have hq : maxNamed q < z := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hqs : maxArgs qs < z := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) h
    simp only [namesOccur, aboveFresh σ z q hq, aboveFreshArgs σ z qs hqs, Bool.false_or]
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.AlphaSizeProof
