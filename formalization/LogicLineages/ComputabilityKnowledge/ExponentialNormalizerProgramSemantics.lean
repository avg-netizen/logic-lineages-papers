module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalizerProgram
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCodeProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProof
public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof

@[expose] public section

/-! Direct Codex proof of the literal compiler's source semantics. The generic
stack simulation maps the already checked source parser through an arbitrary
algebra; it introduces no assumed AST computability or correctness oracle.
The program's genuine primitive-recursive certificates are separate.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramSemantics

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open ExponentialNormalizer ExponentialNormalizerProgram
open ExponentialNormalFormCodeOperations ExponentialNormalFormProductCode
open ExponentialHereditaryCodecProof ExponentialNormalFormCodecProof
open ExponentialNormalFormCodeOperationsProof
open FiniteComparisonEnumeration CircuitReduction

def interpret {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) : Expr Nat → α
  | .one => one
  | .var i => variableValue i
  | .add a b => addition (interpret one variableValue addition exponential a)
      (interpret one variableValue addition exponential b)
  | .emul a b => exponential (interpret one variableValue addition exponential a)
      (interpret one variableValue addition exponential b)

theorem processStep_map {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (t : Token) (es : List (Expr Nat)) :
    processStep one variableValue addition exponential d t
      (es.map (interpret one variableValue addition exponential)) =
    (syntaxStep d t es).map (fun out => out.map (interpret one variableValue addition exponential)) := by
  rcases t with ⟨tag, i⟩
  rcases tag with _ | _ | _ | _ | tag
  · rfl
  · by_cases hi : i < d <;> simp [processStep, syntaxStep, interpret, hi]
  · cases es with
    | nil => rfl
    | cons a es => cases es <;> rfl
  · cases es with
    | nil => rfl
    | cons a es => cases es <;> rfl
  · rfl

theorem processStack_map {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (ts : List Token) :
    processStack one variableValue addition exponential d ts =
      (syntaxStack d ts).map (fun es => es.map (interpret one variableValue addition exponential)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      change (processStack one variableValue addition exponential d ts).bind
        (processStep one variableValue addition exponential d t) =
        ((syntaxStack d ts).bind (syntaxStep d t)).map
          (fun es => es.map (interpret one variableValue addition exponential))
      rw [ih]
      cases hs : syntaxStack d ts with
      | none => rfl
      | some es => exact processStep_map one variableValue addition exponential d t es

theorem processCode_sim {α : Type} (one : α) (variableValue : Nat → α)
    (addition exponential : α → α → α) (d : Nat) (raw : List Nat) :
    processCode one variableValue addition exponential d raw =
      (decodeExpr d raw).map (interpret one variableValue addition exponential) := by
  cases ht : tokenize raw with
  | none => simp [processCode, decodeExpr, ht]
  | some ts =>
      cases hs : syntaxStack d ts with
      | none => simp [processCode, decodeExpr, ht, processStack_map, hs]
      | some es =>
          cases es with
          | nil => simp [processCode, decodeExpr, ht, processStack_map, hs]
          | cons a es => cases es with
            | nil => simp [processCode, decodeExpr, ht, processStack_map, hs]
            | cons b es => simp [processCode, decodeExpr, ht, processStack_map, hs]

theorem finite_rename_bounded (d : Nat) (e : Expr (Fin d)) : Bounded d (e.rename Fin.val) := by
  induction e with
  | one => trivial
  | var i => exact i.isLt
  | add a b ha hb => exact ⟨ha, hb⟩
  | emul a b ha hb => exact ⟨ha, hb⟩

theorem decode_finite (d : Nat) (e : Expr (Fin d)) :
    decodeExpr d (encodeExpr (e.rename Fin.val)) = some (e.rename Fin.val) :=
  (FiniteComparisonEnumerationProof.expressionDecoderExact d _ _).mpr
    ⟨rfl, finite_rename_bounded d e⟩

theorem interpret_row (d H : Nat) (e : Expr (Fin d)) :
    interpret (oneRow d H) (variableRow d H) (additionRow d H) (exponentialRow d H)
      (e.rename Fin.val) = expressionRow d H e := by
  induction e with
  | one => rfl
  | var i => rfl
  | add a b ha hb => simp only [Expr.rename, interpret, expressionRow, ha, hb]
  | emul a b ha hb => simp only [Expr.rename, interpret, expressionRow, ha, hb]

theorem interpret_depth (d : Nat) (e : Expr (Fin d)) :
    interpret 0 (fun _ => 0) Nat.max (fun a b => max a b + 1) (e.rename Fin.val) = e.depth := by
  induction e with
  | one => rfl
  | var i => rfl
  | add a b ha hb => simp only [Expr.rename, interpret, Expr.depth, ha, hb]
  | emul a b ha hb => simp only [Expr.rename, interpret, Expr.depth, ha, hb]

theorem literalCompilation : Comparators.ExponentialNormalizerProgram.LiteralCompilation := by
  intro d H e
  unfold compileAt
  rw [processCode_sim, decode_finite]
  simp only [Option.map_some, interpret_row]

theorem exactDepth : Comparators.ExponentialNormalizerProgram.ExactDepth := by
  intro d e
  unfold depthCode
  rw [processCode_sim, decode_finite]
  simp only [Option.map_some, interpret_depth]

theorem rawDomain : Comparators.ExponentialNormalizerProgram.RawDomain := by
  intro d H raw
  constructor <;> simp only [compileAt, depthCode, processCode_sim, Option.isSome_map]

theorem row_index (H h : Nat) (F : Nat → Nat) (hh : h ≤ H) :
    ((List.range (H + 1)).map F).getD h 0 = F h :=
  getD_map_range (H + 1) F (Nat.lt_succ_of_le hh)

theorem rowRepresentation : Comparators.ExponentialNormalizerProgram.RowRepresentation := by
  intro d H e
  induction e with
  | one =>
      refine ⟨by simp [expressionRow, oneRow], ?_⟩
      intro h hh
      have hx := row_index H h (fun k => constantCode d k 1) hh
      simpa only [expressionRow, oneRow, hx, normalizeAt] using
        And.intro (constantCode_canonical d h 1) (constantCode_decode d h 1)
  | var i =>
      refine ⟨by simp [expressionRow, variableRow], ?_⟩
      intro h hh
      have hx := row_index H h (fun k => variableCode d k i.val) hh
      simpa only [expressionRow, variableRow, hx, normalizeAt] using variableCodes d h i
  | add a b ha hb =>
      refine ⟨by simp [expressionRow, additionRow], ?_⟩
      intro h hh
      have hx : (expressionRow d H (.add a b)).getD h 0 =
          addCode d h ((expressionRow d H a).getD h 0) ((expressionRow d H b).getD h 0) :=
        row_index H h _ hh
      simp only [hx]
      refine ⟨(additionCodes d h _ _).1, ?_⟩
      rw [(additionCodes d h _ _).2, (ha.2 h hh).2, (hb.2 h hh).2]
      rfl
  | emul a b ha hb =>
      refine ⟨by simp [expressionRow, exponentialRow], ?_⟩
      intro h hh
      let F : Nat → Nat := fun k =>
        match k with
        | 0 => zeroCode d 0
        | k + 1 => exponentialProductCode d k ((expressionRow d H a).getD k 0)
            ((expressionRow d H b).getD k 0)
      have hx := row_index H h F hh
      have hc : CodeCanonical d h (F h) ∧
          formDecode d h (F h) = normalizeAt (.emul a b) h := by
        cases h with
        | zero => exact ⟨zeroCode_canonical d 0, zeroCode_decode d 0⟩
        | succ h =>
            have hh' : h ≤ H := Nat.le_trans (Nat.le_succ h) hh
            refine ⟨(ExponentialNormalFormProductCodeProof.sourceImplementation d h _ _).1, ?_⟩
            change formDecode d (h + 1) (exponentialProductCode d h
              ((expressionRow d H a).getD h 0) ((expressionRow d H b).getD h 0)) = _
            rw [(ExponentialNormalFormProductCodeProof.sourceImplementation d h _ _).2,
              (ha.2 h hh').2, (hb.2 h hh').2]
            rfl
      exact Eq.mpr (congrArg (fun n => CodeCanonical d h n ∧
        formDecode d h n = normalizeAt (.emul a b) h) hx) hc

theorem fullEffectiveNormalization : Comparators.ExponentialNormalizerProgram.FullEffectiveNormalization := by
  intro d e
  let n := (expressionRow d e.depth e).getD e.depth 0
  have hn := (rowRepresentation d e.depth e).2 e.depth (Nat.le_refl _)
  have hm := ExponentialNormalizerProof.boundedNormalization d e e.depth (Nat.le_refl _)
  refine ⟨n, ?_, hn.1, ?_, ?_⟩
  · simp [normalizeCode, exactDepth d e, literalCompilation d e.depth e, n]
  · rw [hn.2]
    exact hm.1
  · intro ρ
    rw [hn.2]
    exact hm.2 ρ

end LogicLineages.ComputabilityKnowledge.ExponentialNormalizerProgramSemantics
