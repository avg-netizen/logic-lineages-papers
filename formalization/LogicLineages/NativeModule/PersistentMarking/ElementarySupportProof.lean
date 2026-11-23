module

public import LogicLineages.NativeModule.PersistentMarking.ComparisonTargets
public import LogicLineages.NativeModule.PersistentMarking.OpeningFoundationProof
public import LogicLineages.NativeModule.PersistentMarking.SpineMarkingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ElementarySupportProof
open Spine NameBridge

mutual
 def nodes : Expr → Nat
   | .free _ _ | .bound _ _ => 1
   | .lam _ body => 1 + nodes body
   | .head _ base => 1 + argsNodes base
   | .marked _ _ base extras => 1 + argsNodes base + argsNodes extras
 def argsNodes : Args → Nat
   | .nil => 0
   | .cons q qs => 1 + nodes q + argsNodes qs
end

def spineDepth : Expr → Nat
  | .lam _ body => 1 + spineDepth body
  | _ => 0

mutual
 theorem openNodes (σ : Ty) (x depth : Nat) (q : Expr) :
    nodes (substitute (.cons (.free σ x) .nil) depth q) = nodes q := by
  cases q with
  | free δ y => rfl
  | bound δ i =>
    by_cases hi : i < depth
    · simp [substitute, hi, nodes]
    · cases hn : i-depth with
      | zero => simp [substitute, hi, hn, Args.get, shift, nodes]
      | succ n => simp [substitute, hi, hn, Args.get, nodes]
  | lam δ body => simp only [substitute, nodes, openNodes σ x (depth+1) body]
  | head f base => simp only [substitute, nodes, openArgsNodes σ x depth base]
  | marked f τ base extras => simp only [substitute, nodes, openArgsNodes σ x depth base, openArgsNodes σ x depth extras]
 termination_by sizeOf q
 theorem openArgsNodes (σ : Ty) (x depth : Nat) (qs : Args) :
    argsNodes (substituteArgs (.cons (.free σ x) .nil) depth qs) = argsNodes qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs, argsNodes, openNodes σ x depth q, openArgsNodes σ x depth qs]
 termination_by sizeOf qs
end

mutual
 theorem openValid (S : Signature) (σ : Ty) (x depth : Nat) (q : Expr) (h : Valid S q) :
    Valid S (substitute (.cons (.free σ x) .nil) depth q) := by
  cases q with
  | free δ y => trivial
  | bound δ i =>
    by_cases hi : i < depth
    · simp [substitute, hi, Valid]
    · cases hn : i-depth with
      | zero => simp [substitute, hi, hn, Args.get, shift, Valid]
      | succ n => simp [substitute, hi, hn, Args.get, Valid]
  | lam δ body => exact openValid S σ x (depth+1) body h
  | head f base => exact ⟨h.1,openArgsValid S σ x depth base h.2⟩
  | marked f τ base extras => exact ⟨h.1,openArgsValid S σ x depth base h.2.1,openArgsValid S σ x depth extras h.2.2⟩
 termination_by sizeOf q
 theorem openArgsValid (S : Signature) (σ : Ty) (x depth : Nat) (qs : Args) (h : ValidArgs S qs) :
    ValidArgs S (substituteArgs (.cons (.free σ x) .nil) depth qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨openValid S σ x depth q h.1,openArgsValid S σ x depth qs h.2⟩
 termination_by sizeOf qs
end

mutual
 theorem openOrdinary (σ : Ty) (x depth : Nat) (q : Expr) (h : Ordinary q) :
    Ordinary (substitute (.cons (.free σ x) .nil) depth q) := by
  cases q with
  | free δ y => trivial
  | bound δ i =>
    by_cases hi : i < depth
    · simp [substitute, hi, Ordinary]
    · cases hn : i-depth with
      | zero => simp [substitute, hi, hn, Args.get, shift, Ordinary]
      | succ n => simp [substitute, hi, hn, Args.get, Ordinary]
  | lam δ body => exact openOrdinary σ x (depth+1) body h
  | head f base => exact openArgsOrdinary σ x depth base h
  | marked f τ base extras => exact False.elim h
 termination_by sizeOf q
 theorem openArgsOrdinary (σ : Ty) (x depth : Nat) (qs : Args) (h : OrdinaryArgs qs) :
    OrdinaryArgs (substituteArgs (.cons (.free σ x) .nil) depth qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨openOrdinary σ x depth q h.1,openArgsOrdinary σ x depth qs h.2⟩
 termination_by sizeOf qs
end

theorem openingPaper (S : Signature) (σ τ : Ty) (x : Nat) (body : Expr)
    (h : PaperTerm S (.lam σ body) (.arrow σ τ)) : PaperTerm S (openBody σ x body) τ := by
  obtain ⟨ht,hv⟩ := h
  cases ht with
  | lam hb => exact ⟨OpeningFoundationProof.openingTyped σ τ body x hb, openValid S σ x 0 body hv⟩

theorem markSubstitution (values : Args) (depth : Nat) (q r : Expr) (h : mark q = some r) :
    mark (substitute values depth q) = some (substitute values depth r) := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base => simp only [mark,Option.some.injEq] at h; subst r; rfl
  | marked f τ base extras => simp only [mark,Option.some.injEq] at h; subst r; rfl
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark,hm] at h
    | some b =>
      simp only [mark,hm,Option.map_some,Option.some.injEq] at h
      subst r
      simp only [substitute,mark,markSubstitution values (depth+1) body b hm,Option.map_some]
termination_by sizeOf q

theorem markNames (n : Name) (q r : Expr) (h : mark q = some r) : freeOccurs n q = freeOccurs n r := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base =>
    simp only [mark,Option.some.injEq] at h
    subst r
    simp [freeOccurs,freeOccursArgs]
  | marked f τ base extras => simp only [mark,Option.some.injEq] at h; subst r; rfl
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark,hm] at h
    | some b =>
      simp only [mark,hm,Option.map_some,Option.some.injEq] at h
      subst r
      exact markNames n body b hm
termination_by sizeOf q

theorem markedSpineDepth (values : Args) (depth : Nat) (q r : Expr) (h : mark q = some r) :
    spineDepth (substitute values depth q) = spineDepth q := by
  cases q with
  | free σ x => simp [mark] at h
  | bound σ i => simp [mark] at h
  | head f base => rfl
  | marked f τ base extras => rfl
  | lam σ body =>
    cases hm : mark body with
    | none => simp [mark,hm] at h
    | some b => simp only [substitute,spineDepth,markedSpineDepth values (depth+1) body b hm]
termination_by sizeOf q
end LogicLineages.PersistentMarking.ElementarySupportProof
