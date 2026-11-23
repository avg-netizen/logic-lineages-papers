module

public import LogicLineages.NativeModule.PersistentMarking.StructuralStabilityTargets
public import LogicLineages.NativeModule.PersistentMarking.AlphaEncodingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ClosingNamedProof
open Spine NameBridge StructuralContext

mutual
 theorem encodeClosing (name : Name) (locals : List Name) (q : Term) :
    encode (locals ++ [name]) q = freeSub (closingMap name) locals.length (encode locals q) := by
  cases q with
  | var σ x =>
    cases hl : nameLookup locals (σ,x) with
    | some i => simp [encode,AlphaEncodingProof.lookupAppend,hl,freeSub]
    | none =>
      by_cases he : (σ,x) = name
      · subst name
        simp [encode,AlphaEncodingProof.lookupAppend,hl,nameLookup,freeSub,closingMap,shift]
      · simp [encode,AlphaEncodingProof.lookupAppend,hl,nameLookup,freeSub,closingMap,he,shift]
  | lam σ x q =>
    have hh := encodeClosing name ((σ,x)::locals) q
    simpa only [List.cons_append,encode,freeSub,List.length_cons] using congrArg (Expr.lam σ) hh
  | head f qs => exact congrArg (Expr.head f) (encodeClosingArgs name locals qs)
  | marked f τ qs es =>
    simp only [encode,freeSub,encodeClosingArgs name locals qs,encodeClosingArgs name locals es]
 termination_by sizeOf q
 theorem encodeClosingArgs (name : Name) (locals : List Name) (qs : List Term) :
    encodeArgs (locals ++ [name]) qs = freeSubArgs (closingMap name) locals.length (encodeArgs locals qs) := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    simp only [encodeArgs,freeSubArgs,encodeClosing name locals q,encodeClosingArgs name locals qs]
 termination_by sizeOf qs
end

theorem namedClosing : StructuralStabilityTargets.NamedClosing := by
  intro name q
  exact encodeClosing name [] q

theorem encodeAppend (env : List Name) (xs ys : List Term) :
    encodeArgs env (xs ++ ys) = (encodeArgs env xs).append (encodeArgs env ys) := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append,encodeArgs,Args.append,ih]

theorem namedFill : StructuralStabilityTargets.NamedFill := by
  intro C q
  induction C with
  | hole => rfl
  | head f before inside after ih =>
    simp only [StructuralContext.namedFill,encode,encodeAppend,encodeArgs,
      encodeContext,fill,ih]
  | bind name inside ih =>
    change Expr.lam name.1 (encode [name] (StructuralContext.namedFill inside q)) = _
    rw [namedClosing name (StructuralContext.namedFill inside q),ih]
    rfl
end LogicLineages.PersistentMarking.ClosingNamedProof
