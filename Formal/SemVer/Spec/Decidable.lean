import SemVer.Spec.Precedence

/-!
# 優先順位の決定可能性

仕様の関係を具体例で評価できるようにするためのインスタンス。仕様の意味は変えない。
-/

namespace SemVer.Spec

instance (a b : Byte) : Decidable (AsciiLt a b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

/-- `LexLt` の判定。 -/
def LexLt.decidable {α : Type} [DecidableEq α] (lt : α → α → Prop) [DecidableRel lt] :
    (as bs : List α) → Decidable (LexLt lt as bs)
  | [], [] => isFalse (fun h => h)
  | [], _ :: _ => isTrue True.intro
  | _ :: _, [] => isFalse (fun h => h)
  | a :: as, b :: bs =>
    have : Decidable (LexLt lt as bs) := LexLt.decidable lt as bs
    inferInstanceAs (Decidable (lt a b ∨ (a = b ∧ LexLt lt as bs)))

instance {α : Type} [DecidableEq α] (lt : α → α → Prop) [DecidableRel lt] (as bs : List α) :
    Decidable (LexLt lt as bs) :=
  LexLt.decidable lt as bs

instance PreReleaseId.Lt.decidable : (a b : PreReleaseId) → Decidable (a.Lt b)
  | .numeric a, .numeric b => inferInstanceAs (Decidable (a < b))
  | .alphanumeric a, .alphanumeric b => inferInstanceAs (Decidable (LexLt AsciiLt a b))
  | .numeric _, .alphanumeric _ => isTrue True.intro
  | .alphanumeric _, .numeric _ => isFalse (fun h => h)

instance PreReleaseLt.decidable : (p q : List PreReleaseId) → Decidable (PreReleaseLt p q)
  | [], _ => isFalse (fun h => h)
  | _ :: _, [] => isTrue True.intro
  | a :: as, b :: bs =>
    inferInstanceAs (Decidable (LexLt PreReleaseId.Lt (a :: as) (b :: bs)))

instance (v w : Version) : Decidable (v.Lt w) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (v w : Version) : Decidable (v.PrecedenceEq w) :=
  inferInstanceAs (Decidable (_ ∧ _))

end SemVer.Spec
