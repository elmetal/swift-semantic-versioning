import SemVer.Spec.Precedence

/-!
# 順序の一般論

狭義全順序の定義と、辞書式順序 `LexLt` がそれを保つことの証明。
-/

namespace SemVer

/-- 狭義全順序: 非反射的、推移的、かつ任意の 2 元が比較可能か等しい。 -/
structure StrictTotalOrder {α : Type} (lt : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  trichotomous : ∀ a b, lt a b ∨ a = b ∨ lt b a

/-- 自然数の `<` は狭義全順序。 -/
theorem natLt_strictTotalOrder : StrictTotalOrder (fun a b : Nat => a < b) where
  irrefl := Nat.lt_irrefl
  trans := fun _ _ _ => Nat.lt_trans
  trichotomous := Nat.lt_trichotomy

namespace Spec

variable {α : Type} {lt : α → α → Prop}

theorem LexLt.nil_nil : ¬ LexLt lt [] [] := fun h => h

theorem LexLt.nil_cons {b : α} {bs : List α} : LexLt lt [] (b :: bs) := True.intro

theorem LexLt.cons_nil {a : α} {as : List α} : ¬ LexLt lt (a :: as) [] := fun h => h

theorem LexLt.cons_cons {a b : α} {as bs : List α} :
    LexLt lt (a :: as) (b :: bs) ↔ lt a b ∨ (a = b ∧ LexLt lt as bs) := Iff.rfl

theorem LexLt.irrefl (h : ∀ a, ¬ lt a a) (as : List α) : ¬ LexLt lt as as := by
  induction as with
  | nil => exact LexLt.nil_nil
  | cons a as ih =>
    intro h'
    rcases LexLt.cons_cons.mp h' with h' | ⟨_, h'⟩
    · exact h a h'
    · exact ih h'

theorem LexLt.trans (h : ∀ a b c, lt a b → lt b c → lt a c) (as bs cs : List α)
    (h₁ : LexLt lt as bs) (h₂ : LexLt lt bs cs) : LexLt lt as cs := by
  induction as generalizing bs cs with
  | nil =>
    cases bs with
    | nil => exact absurd h₁ LexLt.nil_nil
    | cons b bs =>
      cases cs with
      | nil => exact absurd h₂ LexLt.cons_nil
      | cons c cs => exact LexLt.nil_cons
  | cons a as ih =>
    cases bs with
    | nil => exact absurd h₁ LexLt.cons_nil
    | cons b bs =>
      cases cs with
      | nil => exact absurd h₂ LexLt.cons_nil
      | cons c cs =>
        rcases LexLt.cons_cons.mp h₁ with hab | ⟨rfl, hab⟩
        · rcases LexLt.cons_cons.mp h₂ with hbc | ⟨rfl, _⟩
          · exact LexLt.cons_cons.mpr (.inl (h _ _ _ hab hbc))
          · exact LexLt.cons_cons.mpr (.inl hab)
        · rcases LexLt.cons_cons.mp h₂ with hbc | ⟨rfl, hbc⟩
          · exact LexLt.cons_cons.mpr (.inl hbc)
          · exact LexLt.cons_cons.mpr (.inr ⟨rfl, ih _ _ hab hbc⟩)

theorem LexLt.trichotomous (h : ∀ a b, lt a b ∨ a = b ∨ lt b a) (as bs : List α) :
    LexLt lt as bs ∨ as = bs ∨ LexLt lt bs as := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact .inr (.inl rfl)
    | cons b bs => exact .inl LexLt.nil_cons
  | cons a as ih =>
    cases bs with
    | nil => exact .inr (.inr LexLt.nil_cons)
    | cons b bs =>
      rcases h a b with hab | rfl | hba
      · exact .inl (LexLt.cons_cons.mpr (.inl hab))
      · rcases ih bs with h' | rfl | h'
        · exact .inl (LexLt.cons_cons.mpr (.inr ⟨rfl, h'⟩))
        · exact .inr (.inl rfl)
        · exact .inr (.inr (LexLt.cons_cons.mpr (.inr ⟨rfl, h'⟩)))
      · exact .inr (.inr (LexLt.cons_cons.mpr (.inl hba)))

/-- 要素の順序が狭義全順序なら、辞書式順序も狭義全順序。 -/
theorem LexLt.strictTotalOrder (h : StrictTotalOrder lt) : StrictTotalOrder (LexLt lt) where
  irrefl := LexLt.irrefl h.irrefl
  trans := LexLt.trans h.trans
  trichotomous := LexLt.trichotomous h.trichotomous

/-- 要素ごとの順序と等しさを保つ写像は、辞書式順序も保つ。 -/
theorem LexLt.map_iff {β : Type} {lt' : β → β → Prop} {f : α → β} :
    ∀ (as bs : List α),
      (∀ a ∈ as, ∀ b ∈ bs, (lt a b ↔ lt' (f a) (f b))) →
      (∀ a ∈ as, ∀ b ∈ bs, (a = b ↔ f a = f b)) →
      (LexLt lt as bs ↔ LexLt lt' (as.map f) (bs.map f))
  | [], [], _, _ => Iff.rfl
  | [], _ :: _, _, _ => Iff.rfl
  | _ :: _, [], _, _ => Iff.rfl
  | a :: as, b :: bs, hlt, heq =>
    or_congr (hlt a (by simp) b (by simp))
      (and_congr (heq a (by simp) b (by simp))
        (LexLt.map_iff as bs
          (fun x hx y hy => hlt x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
          (fun x hx y hy => heq x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))))

end Spec

end SemVer
