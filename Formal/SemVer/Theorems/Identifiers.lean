import SemVer.Spec.Grammar

/-!
# 識別子の特徴づけ

BNF の再帰的な定義を、「すべてのバイトが条件を満たす」形の同値な条件に言い換える。
言い換えた条件は決定可能なので、各非終端記号の判定インスタンスが得られる。
-/

namespace SemVer.Spec

/-! ## 文字クラスの基本事実 -/

theorem not_isIdentifierCharacter_dot : ¬ IsIdentifierCharacter Ascii.dot := by decide

theorem not_isIdentifierCharacter_plus : ¬ IsIdentifierCharacter Ascii.plus := by decide

theorem isIdentifierCharacter_hyphen : IsIdentifierCharacter Ascii.hyphen := by decide

theorem not_isDigit_dot : ¬ IsDigit Ascii.dot := by decide

theorem not_isDigit_hyphen : ¬ IsDigit Ascii.hyphen := by decide

theorem not_isDigit_plus : ¬ IsDigit Ascii.plus := by decide

theorem not_isPositiveDigit_zero : ¬ IsPositiveDigit Ascii.zero := by decide

theorem IsPositiveDigit.isDigit {c : Byte} (h : IsPositiveDigit c) : IsDigit c := Or.inr h

theorem IsDigit.isIdentifierCharacter {c : Byte} (h : IsDigit c) : IsIdentifierCharacter c :=
  Or.inl h

theorem IsNonDigit.isIdentifierCharacter {c : Byte} (h : IsNonDigit c) :
    IsIdentifierCharacter c := Or.inr h

/-! ## `<digits>` -/

theorem Digits.ne_nil {s : List Byte} (h : Digits s) : s ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem Digits.forall_isDigit {s : List Byte} (h : Digits s) : ∀ c ∈ s, IsDigit c := by
  induction h with
  | single hd =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · cases hc
  | cons hd _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact ih c hc

theorem Digits.of_forall : ∀ s : List Byte, s ≠ [] → (∀ c ∈ s, IsDigit c) → Digits s
  | [], h, _ => absurd rfl h
  | [d], _, h => .single (h d (by simp))
  | d :: d' :: ds, _, h =>
    .cons (h d (by simp))
      (Digits.of_forall (d' :: ds) (List.cons_ne_nil _ _)
        (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- 数字列とは、空でなく、すべてのバイトが数字であるもの。 -/
theorem digits_iff (s : List Byte) : Digits s ↔ s ≠ [] ∧ ∀ c ∈ s, IsDigit c :=
  ⟨fun h => ⟨h.ne_nil, h.forall_isDigit⟩, fun h => Digits.of_forall s h.1 h.2⟩

/-! ## `<identifier characters>` -/

theorem IdentifierCharacters.ne_nil {s : List Byte} (h : IdentifierCharacters s) : s ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem IdentifierCharacters.forall_isIdentifierCharacter {s : List Byte}
    (h : IdentifierCharacters s) : ∀ c ∈ s, IsIdentifierCharacter c := by
  induction h with
  | single hd =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · cases hc
  | cons hd _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact ih c hc

theorem IdentifierCharacters.of_forall :
    ∀ s : List Byte, s ≠ [] → (∀ c ∈ s, IsIdentifierCharacter c) → IdentifierCharacters s
  | [], h, _ => absurd rfl h
  | [d], _, h => .single (h d (by simp))
  | d :: d' :: ds, _, h =>
    .cons (h d (by simp))
      (IdentifierCharacters.of_forall (d' :: ds) (List.cons_ne_nil _ _)
        (fun c hc => h c (List.mem_cons_of_mem _ hc)))

theorem identifierCharacters_iff (s : List Byte) :
    IdentifierCharacters s ↔ s ≠ [] ∧ ∀ c ∈ s, IsIdentifierCharacter c :=
  ⟨fun h => ⟨h.ne_nil, h.forall_isIdentifierCharacter⟩,
   fun h => IdentifierCharacters.of_forall s h.1 h.2⟩

/-! ## `<numeric identifier>` -/

theorem NumericIdentifier.ne_nil {s : List Byte} (h : NumericIdentifier s) : s ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

theorem NumericIdentifier.forall_isDigit {s : List Byte} (h : NumericIdentifier s) :
    ∀ c ∈ s, IsDigit c := by
  cases h with
  | zero =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inl rfl
    · cases hc
  | positive hd =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd.isDigit
    · cases hc
  | positiveDigits hd hds =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd.isDigit
    · exact hds.forall_isDigit c hc

/-- 数値識別子とは、`0` そのものか、先頭が `0` でない数字列。 -/
theorem numericIdentifier_iff (s : List Byte) :
    NumericIdentifier s ↔
      s = [Ascii.zero] ∨ ((∀ c ∈ s, IsDigit c) ∧ s ≠ [] ∧ s.head? ≠ some Ascii.zero) := by
  constructor
  · intro h
    cases h with
    | zero => exact .inl rfl
    | positive hd =>
      refine .inr ⟨(NumericIdentifier.positive hd).forall_isDigit, List.cons_ne_nil _ _, ?_⟩
      intro heq
      cases heq
      exact not_isPositiveDigit_zero hd
    | positiveDigits hd hds =>
      refine .inr ⟨(NumericIdentifier.positiveDigits hd hds).forall_isDigit,
        List.cons_ne_nil _ _, ?_⟩
      intro heq
      cases heq
      exact not_isPositiveDigit_zero hd
  · rintro (rfl | ⟨hall, hne, hhead⟩)
    · exact .zero
    · cases s with
      | nil => exact absurd rfl hne
      | cons d ds =>
        have hd : IsPositiveDigit d := by
          rcases hall d (by simp) with hz | hd
          · exact absurd (congrArg some hz) hhead
          · exact hd
        cases ds with
        | nil => exact .positive hd
        | cons d' ds =>
          exact .positiveDigits hd
            (Digits.of_forall _ (List.cons_ne_nil _ _)
              (fun c hc => hall c (List.mem_cons_of_mem _ hc)))

/-! ## `<alphanumeric identifier>` -/

theorem AlphanumericIdentifier.forall_isIdentifierCharacter {s : List Byte}
    (h : AlphanumericIdentifier s) : ∀ c ∈ s, IsIdentifierCharacter c := by
  cases h with
  | nonDigit hc =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hc.isIdentifierCharacter
    · cases hb
  | nonDigitChars hc hcs =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hc.isIdentifierCharacter
    · exact hcs.forall_isIdentifierCharacter b hb
  | charsNonDigit hcs hc =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcs.forall_isIdentifierCharacter b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hc.isIdentifierCharacter
      · cases hb
  | charsNonDigitChars hcs hc hcs' =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hcs.forall_isIdentifierCharacter b hb
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hc.isIdentifierCharacter
      · exact hcs'.forall_isIdentifierCharacter b hb

theorem AlphanumericIdentifier.exists_isNonDigit {s : List Byte}
    (h : AlphanumericIdentifier s) : ∃ c ∈ s, IsNonDigit c := by
  cases h with
  | nonDigit hc => exact ⟨_, by simp, hc⟩
  | nonDigitChars hc _ => exact ⟨_, by simp, hc⟩
  | charsNonDigit _ hc => exact ⟨_, by simp, hc⟩
  | charsNonDigitChars _ hc _ => exact ⟨_, by simp, hc⟩

theorem AlphanumericIdentifier.of_forall_of_exists {s : List Byte}
    (hall : ∀ c ∈ s, IsIdentifierCharacter c) (hex : ∃ c ∈ s, IsNonDigit c) :
    AlphanumericIdentifier s := by
  obtain ⟨c, hmem, hc⟩ := hex
  obtain ⟨l, r, rfl⟩ := List.append_of_mem hmem
  have hl : ∀ b ∈ l, IsIdentifierCharacter b :=
    fun b hb => hall b (List.mem_append.mpr (Or.inl hb))
  have hr : ∀ b ∈ r, IsIdentifierCharacter b :=
    fun b hb => hall b (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hb)))
  cases l with
  | nil =>
    cases r with
    | nil => exact .nonDigit hc
    | cons r₀ rs =>
      exact .nonDigitChars hc (IdentifierCharacters.of_forall _ (List.cons_ne_nil _ _) hr)
  | cons l₀ ls =>
    cases r with
    | nil =>
      exact .charsNonDigit (IdentifierCharacters.of_forall _ (List.cons_ne_nil _ _) hl) hc
    | cons r₀ rs =>
      exact .charsNonDigitChars (IdentifierCharacters.of_forall _ (List.cons_ne_nil _ _) hl) hc
        (IdentifierCharacters.of_forall _ (List.cons_ne_nil _ _) hr)

/-- 英数字識別子とは、すべてが識別子文字で、非数字を 1 つ以上含むもの。 -/
theorem alphanumericIdentifier_iff (s : List Byte) :
    AlphanumericIdentifier s ↔
      (∀ c ∈ s, IsIdentifierCharacter c) ∧ ∃ c ∈ s, IsNonDigit c :=
  ⟨fun h => ⟨h.forall_isIdentifierCharacter, h.exists_isNonDigit⟩,
   fun h => AlphanumericIdentifier.of_forall_of_exists h.1 h.2⟩

/-! ## `<pre-release identifier>` と `<build identifier>` -/

theorem preReleaseIdentifier_iff (s : List Byte) :
    PreReleaseIdentifier s ↔ AlphanumericIdentifier s ∨ NumericIdentifier s := by
  constructor
  · intro h
    cases h with
    | alphanumeric h => exact .inl h
    | numeric h => exact .inr h
  · rintro (h | h)
    · exact .alphanumeric h
    · exact .numeric h

theorem buildIdentifier_iff (s : List Byte) :
    BuildIdentifier s ↔ AlphanumericIdentifier s ∨ Digits s := by
  constructor
  · intro h
    cases h with
    | alphanumeric h => exact .inl h
    | digits h => exact .inr h
  · rintro (h | h)
    · exact .alphanumeric h
    · exact .digits h

theorem PreReleaseIdentifier.forall_isIdentifierCharacter {s : List Byte}
    (h : PreReleaseIdentifier s) : ∀ c ∈ s, IsIdentifierCharacter c := by
  cases h with
  | alphanumeric h => exact h.forall_isIdentifierCharacter
  | numeric h => exact fun c hc => (h.forall_isDigit c hc).isIdentifierCharacter

theorem BuildIdentifier.forall_isIdentifierCharacter {s : List Byte}
    (h : BuildIdentifier s) : ∀ c ∈ s, IsIdentifierCharacter c := by
  cases h with
  | alphanumeric h => exact h.forall_isIdentifierCharacter
  | digits h => exact fun c hc => (h.forall_isDigit c hc).isIdentifierCharacter

/-! ## 判定インスタンス -/

instance (s : List Byte) : Decidable (Digits s) :=
  decidable_of_iff _ (digits_iff s).symm

instance (s : List Byte) : Decidable (IdentifierCharacters s) :=
  decidable_of_iff _ (identifierCharacters_iff s).symm

instance (s : List Byte) : Decidable (NumericIdentifier s) :=
  decidable_of_iff _ (numericIdentifier_iff s).symm

instance (s : List Byte) : Decidable (AlphanumericIdentifier s) :=
  decidable_of_iff _ (alphanumericIdentifier_iff s).symm

instance (s : List Byte) : Decidable (PreReleaseIdentifier s) :=
  decidable_of_iff _ (preReleaseIdentifier_iff s).symm

instance (s : List Byte) : Decidable (BuildIdentifier s) :=
  decidable_of_iff _ (buildIdentifier_iff s).symm

end SemVer.Spec
