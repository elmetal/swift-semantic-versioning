import SemVer.Theorems.Order

/-!
# 優先順位(§11)の性質

`Version.Lt` が「ビルドメタデータを無視した同値 `PrecedenceEq`」を法とする狭義全順序であること、
すなわち任意の 2 つのバージョンについて `v < w`、`v ≈ w`、`w < v` のちょうど 1 つが成り立つことを示す。
Swift の `Comparable` が要求する性質はここから従う。
-/

namespace SemVer.Spec

/-! ## ASCII 順 -/

theorem asciiLt_strictTotalOrder : StrictTotalOrder AsciiLt where
  irrefl := fun a => Nat.lt_irrefl a.toNat
  trans := fun _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂
  trichotomous := fun a b => by
    rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
    · exact .inl h
    · exact .inr (.inl (UInt8.toNat_inj.mp h))
    · exact .inr (.inr h)

/-! ## プレリリース識別子 1 個 -/

theorem PreReleaseId.Lt.irrefl : ∀ a : PreReleaseId, ¬ a.Lt a
  | .numeric n => Nat.lt_irrefl n
  | .alphanumeric s => LexLt.irrefl asciiLt_strictTotalOrder.irrefl s

theorem PreReleaseId.Lt.trans : ∀ a b c : PreReleaseId, a.Lt b → b.Lt c → a.Lt c
  | .numeric _, .numeric _, .numeric _, h₁, h₂ => Nat.lt_trans h₁ h₂
  | .numeric _, .numeric _, .alphanumeric _, _, _ => True.intro
  | .numeric _, .alphanumeric _, .numeric _, _, h₂ => False.elim h₂
  | .numeric _, .alphanumeric _, .alphanumeric _, _, _ => True.intro
  | .alphanumeric _, .numeric _, _, h₁, _ => False.elim h₁
  | .alphanumeric _, .alphanumeric _, .numeric _, _, h₂ => False.elim h₂
  | .alphanumeric _, .alphanumeric _, .alphanumeric _, h₁, h₂ =>
    LexLt.trans asciiLt_strictTotalOrder.trans _ _ _ h₁ h₂

theorem PreReleaseId.Lt.trichotomous : ∀ a b : PreReleaseId, a.Lt b ∨ a = b ∨ b.Lt a
  | .numeric m, .numeric n => by
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact .inl h
    · exact .inr (.inl (congrArg PreReleaseId.numeric h))
    · exact .inr (.inr h)
  | .numeric _, .alphanumeric _ => .inl True.intro
  | .alphanumeric _, .numeric _ => .inr (.inr True.intro)
  | .alphanumeric s, .alphanumeric t => by
    rcases LexLt.trichotomous asciiLt_strictTotalOrder.trichotomous s t with h | h | h
    · exact .inl h
    · exact .inr (.inl (congrArg PreReleaseId.alphanumeric h))
    · exact .inr (.inr h)

theorem PreReleaseId.Lt.strictTotalOrder : StrictTotalOrder PreReleaseId.Lt where
  irrefl := PreReleaseId.Lt.irrefl
  trans := PreReleaseId.Lt.trans
  trichotomous := PreReleaseId.Lt.trichotomous

/-! ## プレリリース部分 -/

theorem PreReleaseLt.irrefl : ∀ p : List PreReleaseId, ¬ PreReleaseLt p p
  | [] => fun h => h
  | a :: as => LexLt.irrefl PreReleaseId.Lt.irrefl (a :: as)

theorem PreReleaseLt.trans :
    ∀ p q r : List PreReleaseId, PreReleaseLt p q → PreReleaseLt q r → PreReleaseLt p r
  | [], _, _, h₁, _ => False.elim h₁
  | _ :: _, [], _, _, h₂ => False.elim h₂
  | _ :: _, _ :: _, [], _, _ => True.intro
  | _ :: _, _ :: _, _ :: _, h₁, h₂ => LexLt.trans PreReleaseId.Lt.trans _ _ _ h₁ h₂

theorem PreReleaseLt.trichotomous :
    ∀ p q : List PreReleaseId, PreReleaseLt p q ∨ p = q ∨ PreReleaseLt q p
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inr (.inr True.intro)
  | _ :: _, [] => .inl True.intro
  | a :: as, b :: bs => LexLt.trichotomous PreReleaseId.Lt.trichotomous (a :: as) (b :: bs)

theorem PreReleaseLt.strictTotalOrder : StrictTotalOrder PreReleaseLt where
  irrefl := PreReleaseLt.irrefl
  trans := PreReleaseLt.trans
  trichotomous := PreReleaseLt.trichotomous

/-- §11.3: プレリリース版は、同じ major.minor.patch の通常バージョンより低い。 -/
theorem PreReleaseLt.cons_nil (a : PreReleaseId) (as : List PreReleaseId) :
    PreReleaseLt (a :: as) [] := True.intro

/-- §11.4.4: 先行する識別子がすべて等しければ、識別子が多い方が高い。 -/
theorem PreReleaseLt.append_right (a : PreReleaseId) (as : List PreReleaseId)
    (b : PreReleaseId) (bs : List PreReleaseId) :
    PreReleaseLt (a :: as) (a :: as ++ b :: bs) := by
  show LexLt PreReleaseId.Lt (a :: as) (a :: (as ++ b :: bs))
  refine LexLt.cons_cons.mpr (.inr ⟨rfl, ?_⟩)
  induction as with
  | nil => exact LexLt.nil_cons
  | cons a' as ih => exact LexLt.cons_cons.mpr (.inr ⟨rfl, ih⟩)

/-! ## バージョン全体 -/

/-- 辞書式比較 1 段分の推移性。 -/
private theorem lexStep_trans {a b c : Nat} {P Q R : Prop} (hPQR : P → Q → R)
    (h₁ : a < b ∨ (a = b ∧ P)) (h₂ : b < c ∨ (b = c ∧ Q)) : a < c ∨ (a = c ∧ R) := by
  rcases h₁ with hab | ⟨rfl, hP⟩
  · rcases h₂ with hbc | ⟨rfl, _⟩
    · exact .inl (Nat.lt_trans hab hbc)
    · exact .inl hab
  · rcases h₂ with hbc | ⟨rfl, hQ⟩
    · exact .inl hbc
    · exact .inr ⟨rfl, hPQR hP hQ⟩

/-- 辞書式比較 1 段分の三分律。 -/
private theorem lexStep_trichotomous {a b : Nat} {P E Q : Prop} (h : P ∨ E ∨ Q) :
    (a < b ∨ (a = b ∧ P)) ∨ (a = b ∧ E) ∨ (b < a ∨ (b = a ∧ Q)) := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hba
  · exact .inl (.inl hab)
  · rcases h with h | h | h
    · exact .inl (.inr ⟨rfl, h⟩)
    · exact .inr (.inl ⟨rfl, h⟩)
    · exact .inr (.inr (.inr ⟨rfl, h⟩))
  · exact .inr (.inr (.inl hba))

/-- どのバージョンも自分自身より低くない。 -/
theorem Version.Lt.irrefl (v : Version) : ¬ v.Lt v := by
  unfold Version.Lt
  rintro (h | ⟨_, h | ⟨_, h | ⟨_, h⟩⟩⟩)
  · exact Nat.lt_irrefl _ h
  · exact Nat.lt_irrefl _ h
  · exact Nat.lt_irrefl _ h
  · exact PreReleaseLt.irrefl _ h

/-- 優先順位は推移的。 -/
theorem Version.Lt.trans {u v w : Version} (h₁ : u.Lt v) (h₂ : v.Lt w) : u.Lt w := by
  unfold Version.Lt at *
  exact lexStep_trans (lexStep_trans (lexStep_trans (PreReleaseLt.trans _ _ _))) h₁ h₂

/-- 優先順位は非対称。 -/
theorem Version.Lt.asymm {v w : Version} (h : v.Lt w) : ¬ w.Lt v :=
  fun h' => Version.Lt.irrefl v (Version.Lt.trans h h')

/-- 任意の 2 つのバージョンは、どちらかが低いか、優先順位が等しい。 -/
theorem Version.Lt.trichotomous (v w : Version) : v.Lt w ∨ v.PrecedenceEq w ∨ w.Lt v := by
  unfold Version.Lt Version.PrecedenceEq
  exact lexStep_trichotomous
    (lexStep_trichotomous (lexStep_trichotomous (PreReleaseLt.trichotomous _ _)))

/-! ## 優先順位の同値 -/

theorem Version.PrecedenceEq.refl (v : Version) : v.PrecedenceEq v := ⟨rfl, rfl, rfl, rfl⟩

theorem Version.PrecedenceEq.symm {v w : Version} (h : v.PrecedenceEq w) : w.PrecedenceEq v :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem Version.PrecedenceEq.trans {u v w : Version}
    (h₁ : u.PrecedenceEq v) (h₂ : v.PrecedenceEq w) : u.PrecedenceEq w :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

/-- 優先順位が等しいバージョンは、左辺で入れ替えても順序が変わらない。 -/
theorem Version.Lt.congr_left {v v' : Version} (w : Version) (h : v.PrecedenceEq v') :
    v.Lt w ↔ v'.Lt w := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  unfold Version.Lt
  rw [h₁, h₂, h₃, h₄]

/-- 優先順位が等しいバージョンは、右辺で入れ替えても順序が変わらない。 -/
theorem Version.Lt.congr_right (v : Version) {w w' : Version} (h : w.PrecedenceEq w') :
    v.Lt w ↔ v.Lt w' := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  unfold Version.Lt
  rw [h₁, h₂, h₃, h₄]

/-- 優先順位が等しいバージョン同士に上下はない。 -/
theorem Version.PrecedenceEq.not_lt {v w : Version} (h : v.PrecedenceEq w) : ¬ v.Lt w :=
  fun h' => Version.Lt.irrefl w ((Version.Lt.congr_left w h).mp h')

/-- §10, §11.1: ビルドメタデータは優先順位に影響しない。 -/
theorem Version.Lt.build_irrelevant (v w : Version) (b b' : List (List Byte)) :
    Version.Lt { v with build := b } { w with build := b' } ↔ v.Lt w := Iff.rfl

/-- §10: ビルドメタデータだけが異なるバージョンは優先順位が等しい。 -/
theorem Version.PrecedenceEq.of_build (v : Version) (b : List (List Byte)) :
    Version.PrecedenceEq { v with build := b } v := ⟨rfl, rfl, rfl, rfl⟩

/-- 優先順位が等しいことと、ビルドメタデータを除いて等しいことは同じ。 -/
theorem Version.precedenceEq_iff (v w : Version) :
    v.PrecedenceEq w ↔ { v with build := [] } = { w with build := [] } := by
  cases v
  cases w
  simp [Version.PrecedenceEq]

end SemVer.Spec
